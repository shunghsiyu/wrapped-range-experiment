#!/usr/bin/env python3
import sys

from z3 import *


# Helpers
BitVec64 = lambda n: BitVec(n, bv=64)
BitVecVal64 = lambda v: BitVecVal(v, bv=64)

class Wrange:
    SIZE = 64 # Working with 64-bit integers
    name: str
    start: BitVecRef
    length: BitVecRef

    def __init__(self, name, start=None, length=None):
        self.name = name
        self.start = BitVec(f'Wrange-{name}-start', bv=self.SIZE) if start is None else start
        assert(self.start.size() == self.SIZE)
        self.length = BitVec(f'Wrange-{name}-length', bv=self.SIZE) if length is None else length
        assert(self.length.size() == self.SIZE)

    def print(self, model):
        name = self.name
        pad = ' ' * (len(self.name) + 1)
        start = model.eval(self.start).as_long()
        length = model.eval(self.length).as_long()
        end = model.eval(self.end).as_long()
        print(f'{name}(start={start}/{hex(start)},\n{pad}length={length}/{hex(length)},\n{pad}end={end}/{hex(end)})')

    def wellformed(self):
        # allow end < start
        return BoolVal(True)

    def reset(self):
        return And(self.start == BitVecVal(0, bv=self.SIZE), self.length == BitVecVal(-1, bv=self.SIZE))

    @property
    def end(self):
        return self.start + self.length

    @property
    def uwrapping(self):
        return ULT(self.end, self.start)

    @property
    def umin(self):
        return If(self.uwrapping, BitVecVal(0, bv=self.SIZE), self.start)

    @property
    def umax(self):
        end = self.start + self.length
        return If(self.uwrapping, BitVecVal(2**self.SIZE - 1, bv=self.SIZE), self.end)

    @property
    def swrapping(self):
        return self.end < self.start

    @property
    def smin(self):
        return If(self.swrapping, BitVecVal(1 << (self.SIZE - 1), bv=self.SIZE), self.start)

    @property
    def smax(self):
        return If(self.swrapping, BitVecVal((2**self.SIZE - 1) >> 1, bv=self.SIZE), self.end)

    def contains(self, val: BitVecRef):
        assert(val.size() == self.SIZE)
        # start <= val <= end
        nonwrapping_cond = And(ULE(self.start, val), ULE(val, self.end))
        # 0 <= val <= end or start <= val <= 2**64-1
        wrapping_cond = Or(
                And(ULE(BitVecVal(0, bv=self.SIZE), val), ULE(val, self.end)),
                And(ULE(self.start, val), ULE(val, BitVecVal(2**self.SIZE - 1, bv=self.SIZE)))
        )
        return If(self.uwrapping, wrapping_cond, nonwrapping_cond)


__all__ = [
        'Wrange',
        'BitVec64',
        'BitVecVal64',
]


def main():
    x = BitVec64('x') # Any possible 64-bit integer x
    w1 = Wrange('w1', start=BitVecVal64(1), length=BitVecVal64(0))
    print(f'Given w1 start={w1.start} length={w1.length}')
    print('\nProving w1 is wellformed')
    prove(
        w1.wellformed(),
    )
    print('\nProving w1.umin is 1')
    prove(
        w1.umin == BitVecVal64(1),
    )
    print('\nProving w1.umax is 1')
    prove(
        w1.umax == BitVecVal64(1),
    )
    print('\nProving w1.smin is 1')
    prove(
        w1.smin == BitVecVal64(1),
    )
    print('\nProving w1.smax is 1')
    prove(
        w1.smax == BitVecVal64(1),
    )
    print('\nProving that w1 contains 1')
    prove(
        w1.contains(BitVecVal64(1)),
    )
    print('\nProving that w1 is a set of {1}')
    prove(
        w1.contains(x) == (x == BitVecVal64(1)),
    )

    w2 = Wrange('w2', start=BitVecVal64(2), length=BitVecVal64(2**64 - 3))
    print(f'\nGiven w2 start={w2.start} length={w2.length}')
    print('\nProving w2 is wellformed')
    prove(
        w2.wellformed(),
    )
    print('\nProving w2.umin is 2')
    prove(
        w2.umin == BitVecVal64(2),
    )
    print('\nProving w2.umax is 2**64-1')
    prove(
        w2.umax == BitVecVal64(2**64 - 1),
    )
    print('\nProving w2.smin is -9223372036854775808/0x8000000000000000')
    prove(
        w2.smin == BitVecVal64(0x8000000000000000),
    )
    print('\nProving w2.smax is 9223372036854775807/0x7fffffffffffffff')
    prove(
        w2.smax == BitVecVal64(0x7fffffffffffffff),
    )
    print('\nProving that w2 contains 2**63 - 1')
    prove(
        w2.contains(BitVecVal64(2**63 - 1)),
    )
    print('\nProving that w2 does NOT contains 1')
    prove(
        Not(w2.contains(BitVecVal64(1))),
    )
    print('\nProving that w2 is a set of {2..2**64-1}')
    prove(
        w2.contains(x) == And(ULE(BitVecVal64(2), x), ULE(x, BitVecVal64(2**64-1))),
    )

    w3 = Wrange('w3', start=BitVecVal64(2), length=BitVecVal64(2**64 - 2))
    print(f'\nGiven w3 start={w3.start} length={w3.length}')
    print('\nProving w3 is also wellformed')
    prove(
        w3.wellformed(),
    )
    print('\nProving w3.umin is 0')
    prove(
        w3.umin == BitVecVal64(0),
    )
    print('\nProving w3.umax is 2**64-1')
    prove(
        w3.umax == BitVecVal64(2**64 - 1),
    )
    print('\nProving w3.smin is -9223372036854775808/0x8000000000000000')
    prove(
        w3.smin == BitVecVal64(0x8000000000000000),
    )
    print('\nProving w3.smax is 9223372036854775807/0x7fffffffffffffff')
    prove(
        w3.smax == BitVecVal64(0x7fffffffffffffff),
    )
    print('\nProving that w3 contains 0')
    prove(
        w3.contains(BitVecVal64(0)),
    )
    print('\nProving that w3 does NOT contain 1')
    prove(
        Not(w3.contains(BitVecVal64(1))),
    )
    print('\nProving that w3 is a union set of ({0} U {2..2**64-1})')
    prove(
        w3.contains(x) == Or(x == BitVecVal64(0), And(ULE(2, x), ULE(x, 2**64-1))),
    )

    w4 = Wrange('w4', start=BitVecVal64(2**64 - 1), length=BitVecVal64(2))
    print(f'\nGiven w4 start={w4.start} length={w4.length}')
    print('\nProving w4 is also wellformed')
    prove(
        w4.wellformed(),
    )
    print('\nProving w4.umin is 0')
    prove(
        w4.umin == BitVecVal64(0),
    )
    print('\nProving w4.umax is 2**64-1')
    prove(
        w4.umax == BitVecVal64(2**64 - 1),
    )
    print('\nProving w4.smin is -1')
    prove(
        w4.smin == BitVecVal64(-1),
    )
    print('\nProving w4.smax is 1')
    prove(
        w4.smax == BitVecVal64(1),
    )
    print('\nProving that w4 contains 0')
    prove(
        w4.contains(BitVecVal64(0)),
    )
    print('\nProving that w4 does contain 2**64-1')
    prove(
        w4.contains(BitVecVal64(2**64-1)),
    )
    print('\nProving that w4 is a union set of ({2**64-1} U {0..1})')
    prove(
        w4.contains(x) == Or(x == BitVecVal64(2**64-1), x == BitVecVal64(0), x == BitVecVal64(1)),
    )

    w = Wrange('w') # Given a Wrange called w
    x = BitVec64('x') # And an 64-bit integer x
    print(f'\nGiven any possible Wrange called w, and any possible 64-bit integer called x')
    print('\nProving if w.contains(x) == True, then w.umin <= x')
    prove(
        Implies(
            And(
                w.wellformed(),
                w.contains(x),
            ),
            ULE(w.umin, x),
        )
    )
    print('\nProving if w.contains(x) == True, then x <= w.umax')
    prove(
        Implies(
            And(
                w.wellformed(),
                w.contains(x),
            ),
            ULE(x, w.umax),
        )
    )

if __name__ == '__main__':
    sys.exit(main())
