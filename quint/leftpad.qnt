module leftpad {
  type Char = { code: int }

  pure val CHARS: Set[Char] = Int.map(i => { code: i })

  var c: Char
  var n: int
  var s: List[Char]
  var output: List[Char]
  var i: int

  pure def max(x: int, y: int): int = if (x > y) x else y

  def pad: int = max(n - s.length(), 0)

  action init = {
    nondet initC = CHARS.oneOf()
    nondet initN = Nat.oneOf()
    nondet initS = CHARS.allLists().oneOf()
    all {
      c' = initC,
      n' = initN,
      s' = initS,
      output' = initS,
      i' = 0,
    }
  }

  action prependPad = all {
    i < pad,
    c' = c,
    n' = n,
    s' = s,
    output' = [c].concat(output),
    i' = i + 1,
  }

  action done = all {
    i >= pad,
    c' = c,
    n' = n,
    s' = s,
    output' = output,
    i' = i,
  }

  action step = any {
    prependPad,
    done,
  }

  def prefixIsPadding(upTo: int): bool =
    and {
      0 <= upTo,
      upTo <= output.length(),
      output.indices().forall(j => j < upTo implies output[j] == c),
    }

  def suffixIsOriginal(offset: int): bool =
    and {
      0 <= offset,
      offset + s.length() <= output.length(),
      s.indices().forall(j => output[offset + j] == s[j]),
    }

  def typeOk: bool = and {
    c.in(CHARS),
    n.in(Nat),
    s.in(CHARS.allLists()),
    output.in(CHARS.allLists()),
    i.in(Nat),
    i <= pad,
  }

  def loopInv: bool = and {
    typeOk,
    output.length() == s.length() + i,
    prefixIsPadding(i),
    suffixIsOriginal(i),
  }

  def correctWhenDone: bool =
    i >= pad implies and {
      output.length() == max(n, s.length()),
      prefixIsPadding(pad),
      suffixIsOriginal(pad),
    }

  def correct: bool = loopInv and correctWhenDone
}

module leftpadExamples {
  import leftpad.*

  action initExample = all {
    c' = { code: 0 },
    n' = 5,
    s' = [{ code: 1 }, { code: 1 }, { code: 0 }],
    output' = [{ code: 1 }, { code: 1 }, { code: 0 }],
    i' = 0,
  }

  run leftpadFive = initExample
    .then(prependPad)
    .then(prependPad)
    .expect(output == [{ code: 0 }, { code: 0 }, { code: 1 }, { code: 1 }, { code: 0 }])
}
