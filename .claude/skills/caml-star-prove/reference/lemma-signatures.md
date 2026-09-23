# Lemma signatures — classifying a saturated counterexample

Once `caml-star-instantiate` has **saturated** (a frontier round adds nothing yet a VC is
still red), the remaining gap needs an inductive *lemma* (or a case split). This file names
the gap from the counterexample. Test the six signatures **in this order** (cheapest fix
first) and take the first whose evidence matches. Every signature's evidence is readable off
the `--solve` output: the JSON countermodel plus the `instantiated terms:` ledger.

Read these first, they recur below:
- **Countermodel** — sort universes, the program variables' values, and each
  function/constructor as a table. A datatype value is **junk** if it is neither a nullary
  constructor nor in the range of any constructor map.
- **Ledger** — the applied terms the VC has in hand, grouped `from the goal / hypotheses /
  instantiate! hints`. The **hypotheses** group shows which constructor each scrutinee took
  (the discriminators) and which recursive calls / guard facts are present.

---

## 1. Missing recursive call (induction hypothesis) — check first

**Evidence.** For a branch-bound variable `r` whose sort matches the target's inductive
parameter, the **goal instantiated at `r`** is *absent* from the hypotheses, while the
goal instantiated at the whole scrutinee is what you are trying to prove. The proof forgot
to recurse on `r`.

**Trap (coverage check).** Do **not** test "is `r` mentioned by some hypothesis?" — an
unrelated helper fact may mention it. Test presence of the **instantiated goal itself**.

**Fix.** One self-call on the uncovered subterm, subject to the **descent rule** (every
argument is the corresponding parameter unchanged or a pattern-bound strict subterm of it,
at least one strict): `let _ = tip_NN a' ... in ...`. Not a lemma — just a call.

---

## 2. Guard lemma

**Evidence.** A function unfolds to `let p = g … in if p then A else B`, and the
countermodel assigns `g …` the value that fires the *wrong* branch, with nothing pinning
it. The stuck goal term stays junk because the equation you need (the `A` branch) never
fires.

**Recipe.** Take the guard instance at the value the proof needs, and **generalize
minimally** — same constant → same variable, never per-occurrence.

**Example (prop04).** Countermodel has `n = nat!0` and `eq_nat(nat!0, nat!0) = false`; the
guard inside `count n (Cons n xs)` is free. Need it `true` ⇒ candidate `eq_nat n n`,
generalized to `∀x. eq_nat x x`:
```
val eq_refl : n:nat -> Lemma(ensures eq_nat n n)
let rec eq_refl n = match n with | Z -> () | S n' -> eq_refl n'
```
called `let _ = eq_refl n in …` in the failing arm. Calling it both asserts the fact **and**
materializes `eq_nat n n`, so the guard connects.

**Example (prop77, `le_neg`).** The `else` branch of `insort` fires when `le x h` is false,
and `sorted` then needs `le h x`. The guard is free ⇒ a totality-shaped guard lemma
`∀x y. ~(le x y) ==> le y x` (an implication ensures — see §5 for the shape).

---

## 3. Shape lemma

**Evidence.** The goal's own step is blocked by an **opaque application** in scrutinee
position (e.g. `add m n` where a match needs to see whether it is `Z`/`S _`), *not* a bare
input variable, and the frontier is empty.

**Recipe — backwards from the blocked step.** Ask which constructor form the opaque
application must take for the blocked equation to fire and land on an available hypothesis;
the instance falls out, then generalize minimally. E.g. to unblock a match on `add m (S n)`:
`∀m n. add m (S n) = S (add m n)`, proved by induction on `m`.

**If no single constructor form suffices** (the head depends on a comparison), fall through
to §5.

---

## 4. Algebraic lemma (argument permutation / regrouping)

**Evidence.** An equality goal whose two sides, evaluated through the ledger's unfoldings
and hypotheses, reach **endpoints identical up to a permutation or regrouping** of one
function's arguments — `S(max B A)` vs `S(max A B)`, or `add (add a b) c` vs `add a (add b c)`.

**Recipe — endpoint anti-unification.** Put fresh variables at the disagreeing positions.

**Example (prop47).** After the two IH calls, `height (mirror (Node l e r))` reduces to
`S(max (height r) (height l))` while the goal's RHS is `S(max (height l) (height r))`. The
endpoints differ by a `max` argument swap ⇒ candidate `∀a b. max a b = max b a`:
```
val max_comm : a:nat -> b:nat -> Lemma(ensures max a b = max b a)
let rec max_comm a b = match a with
  | Z -> (match b with | Z -> () | S b' -> ())
  | S a' -> (match b with | Z -> () | S b' -> max_comm a' b')
```
called `max_comm (height l) (height r)`.

**Goal-as-lemma trap.** The target's own statement, generalized, *always* "checks" against
the countermodel (it is the negated goal's complement). That it would close the VC is
necessary, not sufficient — **acyclicity forbids it** (a helper may not restate the target).
Anti-unify the *endpoints*, not the whole goal.

---

## 5. Conditional preservation

**Evidence.** A Bool goal atom `P (f x a)` with the hypothesis atom `P a` already in
context: a property known of a term is asked of that term pushed through `f`.

**Recipe — conditional anti-unification.** The hypothesis becomes the antecedent:
`∀x a. P a ==> P (f x a)`. In Caml\* this is an implication ensures,
`Lemma(ensures p a ==> p (f x a))`, or a `requires`/`ensures` pair
`Lemma(requires p a)(ensures p (f x a))` — the latter obliges the *caller* to prove `P a`
holds at the instance (supply it from the hypothesis in scope).

---

## 6. Case split (structure, not a lemma)

**Evidence.** Frontier empty **and** the blocking scrutinee is a **bare input variable** of
the target (contrast §3's opaque application); the ledger is typically tiny and the variable
appears with no constructor discriminator pinning its shape.

**Fix.** Wrap the failing branch's body in a `match` on that variable. Each new arm becomes
its own VC (and may itself need instantiations or a further lemma — re-run and re-classify).

---

## The cascade rule

Signatures are tests in a decision order, not disjoint states; recipes hand off:

- test `1 → 2 → 3 → 4 → 5 → 6` (with §3's stall falling through to §5);
- **fixing one gap can surface the next** — a missing recursive call and an algebraic lemma
  can both be absent, and neither fix alone turns the target green; after each fix, re-run
  and re-classify from the top;
- if no signature matches, or your budgeted candidates each leave the target red, that is a
  reportable stop (SKILL.md §6) — give the evidence and the tried candidates; never force a
  fix or conclude "unprovable".

## Summary

| # | Signature | Evidence | Fix |
|---|-----------|----------|-----|
| 1 | missing recursive call | `goal[param := subterm]` absent from hypotheses | descent-checked self-call |
| 2 | guard lemma | guard's value free, wrong branch fires | guard-value lemma, minimal generalization |
| 3 | shape lemma | opaque application blocks a match | constructor-form equation, derived backwards |
| 4 | algebraic lemma | endpoints differ by an argument permutation | endpoint anti-unification |
| 5 | conditional preservation | `P (f x a)` wanted, `P a` known | `P a ==> P (f x a)` |
| 6 | case split | frontier empty, bare-variable scrutinee | `match` on the variable |
