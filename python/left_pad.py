import deal

@deal.pre(lambda _: len(_.c) == 1)
@deal.pre(lambda _: _.n in range(0, 0x10000))  # limit range to 16-bit integers
@deal.ensure(lambda _: len(_.result) == max(_.n, len(_.s)))
@deal.ensure(lambda _: all(_.result[i] == _.c for i in range(max(0, _.n - len(_.s)))))
@deal.ensure(lambda _: all(_.result[max(0, _.n - len(_.s)) + i] == _.s[i] for i in range(len(_.s))))
@deal.pure
def left_pad(c: str, n: int, s: str) -> str:
    pre = c * max(0, n - len(s))
    return f'{pre}{s}'
