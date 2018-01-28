package fse

import (
	"errors"
	"fmt"
)

const (
	tablelogAbsoluteMax = 15
)

func (s *Scratch) readNCount() error {
	var (
		charnum   byte
		previous0 bool
		b         = s.br
	)
	iend := b.remain()
	if iend < 4 {
		return errors.New("input too small")
	}
	bitStream := b.Int32()
	nbBits := uint((bitStream & 0xF) + minTablelog) // extract tableLog
	if nbBits > tablelogAbsoluteMax {
		return errors.New("tableLog too large")
	}
	bitStream >>= 4
	bitCount := uint(4)

	s.actualTableLog = uint8(nbBits)
	remaining := int32((1 << nbBits) + 1)
	threshold := int32(1 << nbBits)
	gotTotal := int32(0)
	nbBits++

	for remaining > 1 {
		if previous0 {
			n0 := charnum
			for (bitStream & 0xFFFF) == 0xFFFF {
				n0 += 24
				if b.off < iend-5 {
					b.advance(2)
					bitStream = b.Int32() >> bitCount
				} else {
					bitStream >>= 16
					bitCount += 16
				}
			}
			for (bitStream & 3) == 3 {
				n0 += 3
				bitStream >>= 2
				bitCount += 2
			}
			n0 += byte(bitStream & 3)
			bitCount += 2
			if n0 > maxSymbolValue {
				return errors.New("maxSymbolValue too small")
			}
			for charnum < n0 {
				s.norm[charnum] = 0
				charnum++
			}

			if b.off <= iend-7 || b.off+int(bitCount>>3) <= iend-4 {
				b.advance(bitCount >> 3)
				bitCount &= 7
				bitStream = b.Int32() >> bitCount
			} else {
				bitStream >>= 2
			}
		}

		max := (2*(threshold) - 1) - (remaining)
		var count int32

		if (bitStream & (threshold - 1)) < max {
			count = bitStream & (threshold - 1)
			bitCount += nbBits - 1
		} else {
			count = bitStream & (2*threshold - 1)
			if count >= threshold {
				count -= max
			}
			bitCount += nbBits
		}

		count-- // extra accuracy
		if count < 0 {
			// -1 means +1
			remaining += count
			gotTotal -= count
		} else {
			remaining -= count
			gotTotal += count
		}
		s.norm[charnum] = int16(count)
		charnum++
		previous0 = count == 0
		for remaining < threshold {
			nbBits--
			threshold >>= 1
		}
		if b.off <= iend-7 || b.off+int(bitCount>>3) <= iend-4 {
			b.advance(bitCount >> 3)
			bitCount &= 7
		} else {
			bitCount -= (uint)(8 * (iend - 4 - b.off))
			b.off = iend - 4
		}
		bitStream = b.Int32() >> (bitCount & 31)
	}
	s.symbolLen = uint16(charnum)
	if remaining != 1 {
		return fmt.Errorf("corruption detected (remaining %d != 1)", remaining)
	}
	if bitCount > 32 {
		return fmt.Errorf("corruption detected (bitCount %d > 32)", bitCount)
	}
	if gotTotal != 1<<s.actualTableLog {
		return fmt.Errorf("corruption detected (total %d != %d)", gotTotal, 1<<s.actualTableLog)
	}
	b.advance((bitCount + 7) >> 3)
	s.br = b
	return nil
}

type decSymbol struct {
	newState uint16
	symbol   uint8
	nbBits   uint8
}

func (s *Scratch) allocDtable() {
	tableSize := 1 << s.actualTableLog
	if cap(s.decTable) < int(tableSize) {
		s.decTable = make([]decSymbol, tableSize)
	}
	s.decTable = s.decTable[:tableSize]

	if cap(s.ct.tableSymbol) < 256 {
		s.ct.tableSymbol = make([]byte, 256)
	}
	s.ct.tableSymbol = s.ct.tableSymbol[:256]

	if cap(s.ct.stateTable) < 256 {
		s.ct.stateTable = make([]uint16, 256)
	}
	s.ct.stateTable = s.ct.stateTable[:256]
}

func (s *Scratch) buildDtable() error {
	tableSize := uint32(1 << s.actualTableLog)
	highThreshold := tableSize - 1
	s.allocDtable()
	symbolNext := s.ct.stateTable[:256]

	// Init, lay down lowprob symbols
	s.decFast = true
	{
		largeLimit := int16(1 << (s.actualTableLog - 1))
		for i, v := range s.norm[:s.symbolLen] {
			if v == -1 {
				s.decTable[highThreshold].symbol = uint8(i)
				highThreshold--
				symbolNext[i] = 1
			} else {
				if v >= largeLimit {
					s.decFast = false
				}
				symbolNext[i] = uint16(v)
			}
		}
	}
	// Spread symbols
	{
		tableMask := tableSize - 1
		step := tableStep(tableSize)
		position := uint32(0)
		for ss, v := range s.norm[:s.symbolLen] {
			for i := 0; i < int(v); i++ {
				s.decTable[position].symbol = uint8(ss)
				position = (position + step) & tableMask
				for position > highThreshold {
					// lowprob area
					position = (position + step) & tableMask
				}
			}
		}
		if position != 0 {
			// position must reach all cells once, otherwise normalizedCounter is incorrect
			return errors.New("corrupted input (position != 0)")
		}
	}

	// Build Decoding table
	{
		for u, v := range s.decTable {
			symbol := v.symbol
			nextState := symbolNext[symbol]
			symbolNext[symbol] = nextState + 1
			nBits := s.actualTableLog - byte(highBits(uint32(nextState)))
			s.decTable[u].nbBits = nBits
			s.decTable[u].newState = (nextState << nBits) - uint16(tableSize)
		}
	}
	return nil
}

func (s *Scratch) decompress() error {
	var dec decoder
	dec.init(s.br.unread(), s.decTable, s.actualTableLog)

	// Use temp table to avoid bound checks/append penalty.
	var tmp = s.ct.tableSymbol[:256]
	var off uint8

	// Main part
	for dec.off >= 8 {
		tmp[off+0], tmp[off+1] = dec.decTwo()
		tmp[off+2], tmp[off+3] = dec.decTwo()
		off += 4
		if off == 0 {
			s.Out = append(s.Out, tmp...)
			off = 0
		}
	}
	s.Out = append(s.Out, tmp[:off]...)

	// Final bits, a bit more expensive check
	for {
		dec.fill()
		s.Out = append(s.Out, dec.dec1())
		if dec.finished() {
			s.Out = append(s.Out, dec.dec2(), dec.dec1())
			break
		}
		if !dec.finished() {
			s.Out = append(s.Out, dec.dec2())
			if dec.finished() {
				s.Out = append(s.Out, dec.dec1(), dec.dec2())
				break
			}
		}
	}
	return nil
}

type decoder struct {
	bitReader
	state, state2 uint16
	dt            []decSymbol
}

func (d *decoder) init(in []byte, dt []decSymbol, tableLog uint8) {
	d.dt = dt
	d.bitReader.init(in)
	d.state, d.state2 = d.get2Bits(tableLog, tableLog)
}

func (d *decoder) decTwo() (uint8, uint8) {
	n := &d.dt[d.state]
	n2 := &d.dt[d.state2]
	b1, b2 := d.get2Bits(n.nbBits, n2.nbBits)
	d.state = n.newState + b1
	d.state2 = n2.newState + b2
	return n.symbol, n2.symbol
}

func (d *decoder) dec1() uint8 {
	n := &d.dt[d.state]
	lowBits := d.getBits(n.nbBits)
	d.state = n.newState + lowBits
	return n.symbol
}

func (d *decoder) dec2() uint8 {
	n := &d.dt[d.state2]
	lowBits := d.getBits(n.nbBits)
	d.state2 = n.newState + lowBits
	return n.symbol
}

func Decompress(b []byte, s *Scratch) ([]byte, error) {
	s, err := s.prepare(b)
	if err != nil {
		return nil, err
	}
	s.Out = s.Out[:0]
	err = s.readNCount()
	if err != nil {
		return nil, err
	}
	err = s.buildDtable()
	if err != nil {
		return nil, err
	}
	err = s.decompress()
	if err != nil {
		return nil, err
	}

	return s.Out, nil
}
