use creusot_contracts::*;

#[ensures
  ({let (pl,rl) = ((l@ - s@.len()).max(0), l@.max(s@.len()));
    result@.len() == rl && rl-pl == s@.len() &&
    (forall<i:Int> 0<=i  && i<pl ==> result@[i] == c) &&
    (forall<i:Int> i>=pl && i<rl ==> result@[i] == s@[i-pl])}) ]
pub fn leftpad<C:Copy>(c:C, l:usize, s:&[C])-> Vec<C>
  { let (rl, pl) = (l.max(s.len()), l.saturating_sub(s.len()));
    let (mut r, mut i) = (Vec::<C>::with_capacity(rl), 0usize);

    #[invariant(inv(r))]
    #[invariant(i@>=0 && i@<=pl@ && r@.len()==i@)]
    #[invariant(forall<j:Int> 0<=j && j<i@ ==> r@[j] == c)]
    while i<pl {r.push(c); i+=1}

    #[invariant(inv(r))]
    #[invariant(i@>=pl@ && i@<=rl@ && r@.len()==i@)]
    #[invariant(forall<j:Int> j>=pl@ && j<i@  ==> r@[j] == s@[j-pl@])]
    #[invariant(forall<j:Int> 0<=j   && j<pl@ ==> r@[j] == c)]
    while i<rl {r.push(s[i-pl]); i+=1}
    r                                                                  }
