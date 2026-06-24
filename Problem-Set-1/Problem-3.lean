open Classical
set_option linter.unusedVariables false

-- There's a much more concise way to prove this
-- but I wanted to structure it like a truth table

theorem contrapositive : (p → q) ↔ (¬q → ¬p) :=
  Or.elim (em p)
    (fun hp : p =>
      Or.elim (em q)
        (fun hq : q =>
          Iff.intro
            (fun _ => fun hnq => absurd hq hnq)
            (fun _ => fun _ => hq))
        (fun hnq : ¬q =>
          Iff.intro
            (fun hpq => absurd (hpq hp) hnq)
            (fun hnqnp => absurd hp (hnqnp hnq))))
    (fun hnp : ¬p =>
      Or.elim (em q)
        (fun hq : q =>
          Iff.intro
            (fun _ => fun hnq => absurd hq hnq)
            (fun _ => fun hp => absurd hp hnp))
        (fun hnq : ¬q =>
          Iff.intro
            (fun _ => fun _ => hnp)
            (fun _ => fun hp => absurd hp hnp)))
