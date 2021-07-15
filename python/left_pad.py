import sys
import deal

@deal.pre(lambda _: len(_.c) == 1)
@deal.pre(lambda _: _.n >= 0)
@deal.ensure(lambda _: len(_.result) == max(_.n, len(_.s)))
@deal.ensure(lambda _: all(x == _.c for x in _.result[:-len(_.s)]))
@deal.ensure(lambda _: all(x[0] == x[1] for x in zip(reversed(_.result), reversed(_.s))))
@deal.raises(MemoryError, OverflowError)
@deal.reason(OverflowError, lambda _: _.n - len(_.s) > sys.maxsize)
@deal.has()
def left_pad(c: str, n: int, s: str) -> str:
    pre = c * max(0, n - len(s))
    return f'{pre}{s}'
