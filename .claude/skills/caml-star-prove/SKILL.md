---
name: caml-star-prove
description: >-
  Discharge a Caml* (`.cst`) proof effort end to end: make its lemmas verify by adding
  instantiation hints and, when those are not enough, by hypothesizing, proving, and
  calling the auxiliary lemmas the proof needs. This is the TOP-LEVEL skill for Caml* /
  caml-star proofs — use it whenever a `.cst` lemma fails to verify, the solver prints
  `[counterexample]`, or the user asks to prove / discharge / close / finish a Caml*
  lemma or a `tests/prop*.cst`, or to infer the auxiliary lemmas and instantiations a
  proof is missing. It delegates instantiation to `caml-star-instantiate` and only adds
  proof-side terms (hints, lemmas, calls) — never weakening a spec or editing a definition.
---

# Proving Caml* lemmas: instantiations, then auxiliary lemmas

You are closing a Caml\* proof. Two tools are available and you apply them in order:
**instantiation hints** (cheap, mechanical — the `caml-star-instantiate` skill) and, when
instantiation provably cannot finish, **auxiliary lemmas** you hypothesize from the
counterexample, prove, and call. The process is recursive: proving a lemma may itself need
more instantiations or further lemmas.

## 1. Background: relational abstraction, and the two ways a proof gets stuck

Caml\* does not hand a datatype function to Z3 as a function. It **relationally abstracts**
it: a user function or constructor `f : A → B` becomes a relation `f_rel(args, result)`
with a **functionality** axiom (same args ⇒ same result) and **definitional equations**
from `f`'s body. This keeps queries decidable (EPR) but is deliberately *incomplete*:
**totality is not asserted.** Nothing says every application `f(args)` has a result, nor
that every element of a datatype sort is reachable by constructors. So a Z3 model may
contain **"junk" elements** — an element of sort `nat` that is neither `Z` nor `S` of
anything. A definitional equation such as `max (S a') (S b') = S (max a' b')` is *guarded by
the constructor shape of its arguments* and its right-hand side can only fire once the
witness `S (max a' b')` **exists** in the model. Two distinct absences then cause spurious
counterexamples:

- **A missing witness.** The constructor-of-a-recursive-subresult (`S (max a' b')`) never
  gets materialized, so the guarded equation stays silent and the application lands on junk.
  This is what **instantiations** repair: `instantiate!(e)` forces `e`'s applied subterms
  into the model. Handled entirely by `caml-star-instantiate`.
- **A missing fact.** No finite set of ground terms is enough — the obligation needs an
  inductive theorem (`∀x. eq_nat x x`, `∀a b. max a b = max b a`). This is what **lemmas**
  repair, and it is this skill's core job.

Both repairs are **additive and completeness-only**: they can turn a spurious
`counterexample` into `verified` and can never make a true `verified` false.

## 2. How a lemma works in Caml*

A lemma is an ordinary function whose result type is the `Lemma` sugar:

```
val eq_refl : n:nat -> Lemma(ensures eq_nat n n)     (* desugars to  n:nat -> squash (eq_nat n n) *)
let rec eq_refl n = match n with | Z -> () | S n' -> eq_refl n'
```

**A lemma enters another proof only through a CALL.** `let _ = eq_refl n in body` binds a
proof of `eq_nat n n`; Caml\* lifts that fact into the branch's hypotheses (and materializes
the terms inside it). So the arguments and the branch you call it in are as load-bearing as
the statement — defining a lemma without calling it changes nothing. Consequences:

- **Placement.** Insert a new helper `val`+proof **above** the target (definitions are
  in-file order). Call it in the specific arm whose VC is red, at the instance the
  counterexample names.
- **`requires` lemmas.** `Lemma(requires p)(ensures q)` desugars to `_:squash p -> squash q`
  — the caller must supply a proof of `p` at the instance (usually a hypothesis already in
  scope). Prefer a plain implication ensures `Lemma(ensures p ==> q)` when the antecedent is
  not already proven.
- **A helper's own body generates VCs** that must be discharged like any other — recurse.

## 3. The envelope (hard rule)

**Only ADDITIVE, proof-side edits.** You may add:
- `instantiate!(…)` hints (via `caml-star-instantiate`);
- new `val L … Lemma(…)` declarations together with their `let rec L … =` proofs;
- calls to lemmas (`let _ = L args in …`);
- descent-checked recursive self-calls (see §5);
- a case split — wrapping a failing branch's body in a `match` on a scrutinee.

**Never** modify the target lemma's `Lemma(…)` specification, any datatype declaration, or
any existing (non-lemma) function definition. Never weaken a spec, comment out a property,
or "fix" a definition. If a proof cannot be closed within the envelope, **report it**
(§6) — do not breach the boundary. Audit with `git diff`: the target's spec line, the
datatypes, and the function definitions must appear in zero hunks. **No `assume` survives
to the finished file** (see §4.5).

## 4. Procedure

Run everything from `ocaml/`:

```
cd ocaml && eval "$(opam env)"
dune exec ./main.exe -- --solve tests/<FILE>.cst
```

There is one VC per proof branch, so a lemma with several arms yields several
counterexamples; treat each independently.

**4.1 Instantiation gate.** Invoke the **`caml-star-instantiate`** skill on the file. If it
reports **DISCHARGED** (all VCs `verified`), you are done. Only proceed when it reports
**SATURATED** — the frontier added nothing and VCs are still red. (Never hypothesize a
lemma before instantiation has saturated: a gap that instantiation can close is not a
missing fact.)

**4.2 Intake.** For each still-red VC, read the printed counterexample (the JSON model) and
the `instantiated terms:` ledger, alongside the original program. These, not solver probing,
are your evidence.

**4.3 Classify the gap.** Work through the signatures in `reference/lemma-signatures.md`
(missing recursive call → guard → shape → algebraic → conditional preservation → case
split) and take the first whose evidence matches the countermodel.

**4.4 Hypothesize.** Derive the candidate by the signature's recipe and **generalize
minimally** — same constant → same variable, never per-occurrence (which over-generalizes
to a falsehood). Do not propose the target's own statement generalized (acyclicity; the
"goal-as-lemma trap").

**4.5 Sufficiency check with a temporary `assume val`.** Before investing in a proof,
confirm the *statement* actually closes the target. Declare the helper as an **unproven
axiom** and call it:
```
assume val L : <binders> -> Lemma(ensures <candidate>)
...
  | <failing arm> -> let _ = L <instance args> in <arm body>
```
Re-run. Target now green ⇒ the statement suffices; move to 4.6. Still red ⇒ wrong or
insufficient candidate — re-classify, or the arm may need two facts jointly (add both).
> Note: `assume` in *expression* position (`let _ = assume p in …`) is a no-op in Caml\* —
> it drops `p`. The sufficiency check must use a top-level **`assume val`** as above.

**4.6 Construct and prove.** Delete the `assume` keyword and give `L` a real proof
(`let rec L … = match … `), by induction mirroring the datatype of its inductive parameter.
Keep the call. Re-run.

**4.7 Compose / recurse.** Re-read the result:
- A **helper VC** fails → apply the **instantiation gate** (4.1) to the helper; if it
  saturates still red, the helper has its own lemma gap — recurse from 4.3 for it (this
  costs one unit of lemma depth, §5).
- A **target VC** still fails → re-run the gate and re-classify from 4.3 (the cascade —
  fixing one gap surfaces the next).

**4.8 Verify and minimize.** When the file reports `N verified, 0 counterexamples`, remove
each added lemma, call, and hint in turn and re-run; keep only those whose removal re-breaks
the proof. Finally confirm the finished file contains **zero `assume`** (`grep -n assume
tests/<FILE>.cst` is empty).

## 5. Composition, recursion, and budgets

- **Acyclicity.** A helper may not call or restate the target, directly or transitively.
  Calls to already-proven lemmas are free.
- **Descent rule (every added self-call, in the target or a helper).** Each argument is the
  corresponding parameter unchanged or a pattern-bound *strict* subterm of it, with at least
  one strict. A same-argument self-call would "prove" anything (termination is not checked)
  and is forbidden. Note the justification in the report: `added tip_NN a' …: a' ⊏ a`.
- **Budgets** (only *unproven* conjectures created this session count; proven lemmas are
  free): **lemma-depth ≤ 3** (a chain of conjectures more than three deep → stop and report
  the chain) and **lemma-count ≤ 4** per session (beyond it, report the plan, not a pile).
  Both are overridable by invocation keywords — `depth-limit N`, `lemma-limit N` — for
  proofs beyond TIP scale. Overrides change the numbers, never the semantics: a budget stop
  reports state, it never concludes "unprovable".

## 6. Stop conditions

- **Success** — verify and minimize (§4.8), then report (§7).
- **No candidate closes it** — no signature matches, or your budgeted candidates (2–3 per
  red VC) each leave the target red with the same countermodel shape. Report the tried
  candidates (statement; proven or not; the target's failing VC after the call) and the
  classification evidence. Do **not** conclude "unprovable".
- **Budget hit** — depth or count limit reached; report the conjecture chain for review.
- **Envelope breach required** — every continuation lives in a read-only region: a
  possibly-wrong target spec (every candidate leaves the same countermodel standing), a
  possibly-buggy definition (the countermodel's function table shows the suspect equation),
  or circularity pressure (only the goal itself would close it). Refuse and report what the
  evidence suggests **without** touching the protected region.

## 7. Report format

Per added lemma: statement, signature (§ from the reference), call site + instance
arguments, and depth used. Per added self-call: the descent justification. Any
instantiations added (by the composed sub-skill) and where. Removals from minimization. The
final `N verified, 0 counterexamples` line and confirmation of zero `assume`. On a stop
(§6): the named stop, the evidence, the tried candidates with verdicts, and the suggested
next action explicitly out of scope.

## 8. Worked example — prop04 (guard lemma)

`tip_04 : S (count n xs) = count n (Cons n xs)`. The instantiation gate saturates with the
`Nil`-arm VC still red. Its counterexample:

```
"n": "nat!0", "xs": "Nil",
"eq_nat": { …, "(nat!0, nat!0)": "false", … }
```
and the ledger's goal group holds `count n (Cons n xs)` but nothing pins the guard inside it.

- **Classify.** `count n (Cons n xs)` unfolds to `if eq_nat n n then S (count n xs) else …`;
  the model sets `eq_nat(nat!0, nat!0) = false`, firing the wrong branch. **Guard lemma** (§2).
- **Hypothesize.** Need `eq_nat n n = true`; minimal generalization `∀x. eq_nat x x`.
- **Sufficiency check.** `assume val eq_refl : n:nat -> Lemma(ensures eq_nat n n)` and
  `| Nil -> let _ = eq_refl n in ()` → target verifies (2/2). Statement suffices.
- **Prove.** `let rec eq_refl n = match n with | Z -> () | S n' -> eq_refl n'` (drop
  `assume`). Re-run → **4 verified, 0 counterexamples** (the `Cons` arm already closed via
  its recursive call). `grep assume` empty. Done.

## 9. Worked example — prop47 (algebraic lemma)

`tip_47 : height (mirror t) = height t`, with `height (Node l e r) = S (max (height l)
(height r))` and `mirror (Node l e r) = Node (mirror r) e (mirror l)`. The gate saturates
with the `Node`-arm VC red; the two IH calls `tip_47 l`, `tip_47 r` are present, and the
`max` table in the countermodel never forces the two orderings equal.

- **Classify.** Through the IHs the LHS reduces to `S (max (height r) (height l))` and the
  goal's RHS is `S (max (height l) (height r))` — endpoints differing by a `max` argument
  swap. **Algebraic lemma** (§4). (Not the goal generalized — acyclicity.)
- **Hypothesize.** Endpoint anti-unification → `∀a b. max a b = max b a`.
- **Sufficiency check.** `assume val max_comm : a:nat -> b:nat -> Lemma(ensures max a b = max
  b a)` called `max_comm (height l) (height r)` in the `Node` arm → target verifies.
- **Prove.** induction on both arguments:
  ```
  let rec max_comm a b = match a with
    | Z -> (match b with | Z -> () | S b' -> ())
    | S a' -> (match b with | Z -> () | S b' -> max_comm a' b')
  ```
  Re-run → **6 verified, 0 counterexamples.** `grep assume` empty. Done.

## 10. Reading order

This file drives the loop; open `reference/lemma-signatures.md` at step 4.3 to classify, and
the `caml-star-instantiate` skill is the instantiation gate (steps 4.1 and 4.7). The
verified `tests/prop*.cst` are worked answer keys for the lemma shapes the signatures name.
