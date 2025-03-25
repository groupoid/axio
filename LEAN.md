# Lean Tactics List

This document lists tactics available in Lean as of March 24, 2025, based on the provided documentation. Each tactic includes its name, syntax reference, and a brief description of its functionality.

## Tactics

### `#adaptation_note`
- **Syntax Reference:** `[«tactic#adaptation_note_»]`
- **Description:** Adaptation notes are comments indicating that a piece of code has been modified to accommodate changes in Lean core. They typically require future action or maintenance.

### `#check`
- **Syntax Reference:** `[Mathlib.Tactic.«tactic#check__»]`
- **Description:** The `#check t` tactic elaborates the term `t` and pretty prints it with its type as `e : ty`. If `t` is an identifier, it prints a type declaration for the global constant `t`. Use `#check (t)` to print it as an elaborated expression. Allows stuck typeclass instance problems, which become metavariables in the output.

### `#count_heartbeats`
- **Syntax Reference:** `[Mathlib.CountHeartbeats.«tactic#count_heartbeats_»]`
- **Description:** Counts the heartbeats used by a tactic, e.g., `#count_heartbeats simp`.

### `#count_heartbeats!`
- **Syntax Reference:** `[Mathlib.CountHeartbeats.«tactic#count_heartbeats!_In__»]`
- **Description:** Runs a tactic 10 times (or `n` times with `#count_heartbeats! n in tac`), counting heartbeats and logging the range and standard deviation.

### `#find`
- **Syntax Reference:** `[Mathlib.Tactic.Find.«tactic#find_»]`
- **Description:** (No detailed description provided in the document.)

### `#leansearch`
- **Syntax Reference:** `[LeanSearchClient.leansearch_search_tactic]`
- **Description:** Searches [LeanSearch](https://leansearch.net/) from within Lean. Queries must end with `.` or `?`. Works as a command, term, or tactic, displaying only valid tactics in tactic mode. Example: `#leansearch "If a natural number n is less than m, then the successor of n is less than the successor of m."`.

### `#loogle`
- **Syntax Reference:** `[LeanSearchClient.loogle_tactic]`
- **Description:** Searches [Loogle](https://loogle.lean-lang.org/json) from within Lean. Can be used as a command, term, or tactic, displaying only valid tactics in tactic mode. Supports searching by constant, lemma name substring, subexpression, or main conclusion. Example: `#loogle List ?a → ?a`.

### `#moogle`
- **Syntax Reference:** `[LeanSearchClient.moogle_search_tactic]`
- **Description:** Searches [Moogle](https://www.moogle.ai/api/search) from within Lean. Queries must end with `.` or `?`. Works as a command, term, or tactic, displaying only valid tactics in tactic mode. Example: `#moogle "If a natural number n is less than m, then the successor of n is less than the successor of m."`.

### `#search`
- **Syntax Reference:** `[LeanSearchClient.search_tactic]`
- **Description:** Searches either [Moogle](https://www.moogle.ai/api/search) or [LeanSearch](https://leansearch.net/) based on the `leansearchclient.backend` option. Queries must end with `.` or `?`. In tactic mode without a query string, queries [LeanStateSearch](https://premise-search.com) based on the goal state.

### `#statesearch`
- **Syntax Reference:** `[LeanSearchClient.statesearch_search_tactic]`
- **Description:** Searches [LeanStateSearch](https://premise-search.com) using the current main goal as the query. Options `statesearch.revision` and `statesearch.queries` can set the revision and number of results, respectively.

### `(`
- **Syntax Reference:** `[Lean.Parser.Tactic.paren]`
- **Description:** `(tacs)` executes a list of tactics in sequence without requiring the goal to be closed at the end, unlike `· tacs`. Tactics can be separated by newlines or `;`.

### `<;>`
- **Syntax Reference:** `[Batteries.Tactic.seq_focus]`
- **Description:** `t <;> [t1; t2; ...; tn]` focuses on the first goal, applies `t` to produce `n` subgoals, then applies each `ti` to the corresponding subgoal, collecting the resulting subgoals.

### `<;>`
- **Syntax Reference:** `[Lean.Parser.Tactic.«tactic_<;>_»]`
- **Description:** `tac <;> tac'` runs `tac` on the main goal and `tac'` on each produced goal, concatenating all goals produced by `tac'`.

### `_`
- **Syntax Reference:** `[Batteries.Tactic.tactic_]`
- **Description:** `_` in tactic position acts like `done`, failing and listing goals if any remain. Useful as a placeholder after starting a tactic block like `by _`.

### `abel`
- **Syntax Reference:** `[Mathlib.Tactic.Abel.abel]`
- **Description:** Evaluates equations in additive, commutative monoids and groups. Works as both a tactic and conv tactic. Variants include `abel1`, `abel_nf`, and aggressive versions with `!`.

### `abel!`
- **Syntax Reference:** `[Mathlib.Tactic.Abel.tacticAbel!]`
- **Description:** A more aggressive version of `abel` using a higher reducibility setting to identify atoms.

### `abel1`
- **Syntax Reference:** `[Mathlib.Tactic.Abel.abel1]`
- **Description:** Fails if the target is not an equality provable by commutative monoid/group axioms.

### `abel1!`
- **Syntax Reference:** `[Mathlib.Tactic.Abel.abel1!]`
- **Description:** Aggressive version of `abel1` with a higher reducibility setting.

### `abel_nf`
- **Syntax Reference:** `[Mathlib.Tactic.Abel.abelNF]`
- **Description:** Rewrites group expressions into a normal form. Can be used at hypotheses with `abel_nf at h` and configured with options like `red`, `zetaDelta`, and `recursive`.

### `abel_nf!`
- **Syntax Reference:** `[Mathlib.Tactic.Abel.tacticAbel_nf!__]`
- **Description:** Aggressive version of `abel_nf` with a higher reducibility setting.

### `absurd`
- **Syntax Reference:** `[Batteries.Tactic.tacticAbsurd_]`
- **Description:** Given a proof `h` of `p`, `absurd h` changes the goal to `⊢ ¬ p`. If `p` is `¬q`, the goal becomes `⊢ q`.

### `ac_change`
- **Syntax Reference:** `[Mathlib.Tactic.acChange]`
- **Description:** `ac_change g using n` converts to `g` using `n` steps, followed by `ac_rfl`. Useful for rearranging sums, e.g., `ac_change a + d + e + f + c + g + b ≤ _`.

### `ac_nf`
- **Syntax Reference:** `[Lean.Parser.Tactic.tacticAc_nf_]`
- **Description:** Normalizes equalities up to associative and commutative operators. Can normalize hypotheses and the goal target with `ac_nf at l`.

### `ac_nf0`
- **Syntax Reference:** `[Lean.Parser.Tactic.acNf0]`
- **Description:** Implementation of `ac_nf` without calling `trivial` afterward.

### `ac_rfl`
- **Syntax Reference:** `[Lean.Parser.Tactic.acRfl]`
- **Description:** Proves equalities up to associative and commutative operators, e.g., `a + b + c + d = d + (b + c) + a` with appropriate instances.

### `admit`
- **Syntax Reference:** `[Lean.Parser.Tactic.tacticAdmit]`
- **Description:** Synonym for `sorry`, closing the main goal with a placeholder.

### `aesop`
- **Syntax Reference:** `[Aesop.Frontend.Parser.aesopTactic]`
- **Description:** Tries to solve the goal using rules registered with `@[aesop]`. Supports clauses for customization, e.g., `(add unsafe 50% apply Or.inl)`. `aesop?` prints the proof as a suggestion.

### `aesop?`
- **Syntax Reference:** `[Aesop.Frontend.Parser.aesopTactic?]`
- **Description:** Variant of `aesop` that prints the found proof as a `Try this` suggestion.

### `aesop_cat`
- **Syntax Reference:** `[CategoryTheory.aesop_cat]`
- **Description:** A wrapper for `aesop` adding the `CategoryTheory` rule set and allowing semireducible definition lookup during `intros`. Fails if unable to solve, suitable for auto-params.

### `aesop_cat?`
- **Syntax Reference:** `[CategoryTheory.aesop_cat?]`
- **Description:** Passes a `Try this` suggestion when using `aesop_cat`.

### `aesop_cat_nonterminal`
- **Syntax Reference:** `[CategoryTheory.aesop_cat_nonterminal]`
- **Description:** Variant of `aesop_cat` that does not fail if unable to solve, intended for exploration only.

### `aesop_unfold`
- **Syntax Reference:** `[Aesop.tacticAesop_unfold_]`, `[Aesop.tacticAesop_unfold_At_]`
- **Description:** (No detailed description provided in the document.)

### `algebraize`
- **Syntax Reference:** `[Mathlib.Tactic.tacticAlgebraize__]`
- **Description:** Adds `Algebra` and `IsScalarTower` instances from `RingHom`s and converts `RingHom` properties to `Algebra` properties if `properties := true`.

### `algebraize_only`
- **Syntax Reference:** `[Mathlib.Tactic.tacticAlgebraize_only__]`
- **Description:** Adds only `Algebra` and `IsScalarTower` instances without converting properties tagged with `@[algebraize]`.

### `all_goals`
- **Syntax Reference:** `[Lean.Parser.Tactic.allGoals]`
- **Description:** Runs a tactic on each goal, concatenating resulting goals. Fails if the tactic fails on any goal.

### `and_intros`
- **Syntax Reference:** `[Lean.Parser.Tactic.tacticAnd_intros]`
- **Description:** Applies `And.intro` until no further progress is made.

### `any_goals`
- **Syntax Reference:** `[Lean.Parser.Tactic.anyGoals]`
- **Description:** Applies a tactic to every goal, concatenating successful applications. Fails if the tactic fails on all goals.

### `apply`
- **Syntax Reference:** `[Mathlib.Tactic.tacticApply_At_]`, `[Lean.Parser.Tactic.apply]`, `[Mathlib.Tactic.applyWith]`
- **Description:** Matches the goal against the conclusion of an expression’s type, generating subgoals for unresolved premises. Supports forward reasoning at hypotheses and configuration options.

### `apply?`
- **Syntax Reference:** `[Lean.Parser.Tactic.apply?]`
- **Description:** Searches the environment for applicable theorems, refining the goal with `apply` and resolving conditions with `solve_by_elim`. Optional `using` clause specifies required identifiers.

### `apply_assumption`
- **Syntax Reference:** `[Lean.Parser.Tactic.applyAssumption]`
- **Description:** Applies an assumption matching the goal’s head, with options to specify rules, omit hypotheses, or use attributes. Tries `symm` and `exfalso` if needed.

### `apply_ext_theorem`
- **Syntax Reference:** `[Lean.Elab.Tactic.Ext.applyExtTheorem]`
- **Description:** Applies a single extensionality theorem to the current goal.

### `apply_fun`
- **Syntax Reference:** `[Mathlib.Tactic.applyFun]`
- **Description:** Applies a function to equalities or inequalities in hypotheses or the goal, handling cases like `Monotone`, `StrictMono`, or `Injective` with automatic or explicit discharging.

### `apply_mod_cast`
- **Syntax Reference:** `[Lean.Parser.Tactic.tacticApply_mod_cast_]`
- **Description:** Normalizes casts in the goal and expression, then applies the expression.

### `apply_rfl`
- **Syntax Reference:** `[Lean.Parser.Tactic.applyRfl]`
- **Description:** Similar to `rfl` but without trying `eq_refl` at the end.

### `apply_rules`
- **Syntax Reference:** `[Lean.Parser.Tactic.applyRules]`
- **Description:** Iteratively applies a list of lemmas or hypotheses to solve the goal and subgoals, with options to customize assumptions, depth, and symmetry usage.

### `arith_mult`
- **Syntax Reference:** `[ArithmeticFunction.arith_mult]`
- **Description:** Solves goals of the form `IsMultiplicative f` for arithmetic functions using lemmas tagged with `@[arith_mult]`.

### `arith_mult?`
- **Syntax Reference:** `[ArithmeticFunction.arith_mult?]`
- **Description:** Like `arith_mult` but prints the generated proof term.

### `array_get_dec`
- **Syntax Reference:** `[Array.tacticArray_get_dec]`
- **Description:** Proves `sizeOf arr[i] < sizeOf arr` for well-founded recursions over nested inductives.

### `array_mem_dec`
- **Syntax Reference:** `[Array.tacticArray_mem_dec]`
- **Description:** Proves `sizeOf a < sizeOf arr` given `a ∈ arr` for well-founded recursions.

### `as_aux_lemma`
- **Syntax Reference:** `[Lean.Parser.Tactic.as_aux_lemma]`
- **Description:** Wraps a tactic’s result in an auxiliary lemma to reduce expression size.

### `assumption`
- **Syntax Reference:** `[Lean.Parser.Tactic.assumption]`
- **Description:** Solves the goal using a compatible hypothesis or fails.

### `assumption'`
- **Syntax Reference:** `[Mathlib.Tactic.tacticAssumption']`
- **Description:** Tries `assumption` on all goals, succeeding if it closes at least one.

### `assumption_mod_cast`
- **Syntax Reference:** `[Lean.Parser.Tactic.tacticAssumption_mod_cast_]`
- **Description:** Normalizes casts in the goal and hypotheses with `norm_cast`, then tries to solve using a hypothesis.

### `attempt_all`
- **Syntax Reference:** `[Lean.Parser.Tactic.attemptAll]`
- **Description:** Internal helper for implementing `try?`.

### `aux_group₁`
- **Syntax Reference:** `[Mathlib.Tactic.Group.aux_group₁]`
- **Description:** Auxiliary tactic for `group`, calling the simplifier only.

### `aux_group₂`
- **Syntax Reference:** `[Mathlib.Tactic.Group.aux_group₂]`
- **Description:** Auxiliary tactic for `group`, normalizing exponents with `ring_nf`.

### `bddDefault`
- **Syntax Reference:** `[tacticBddDefault]`
- **Description:** Automatically fills boundedness proofs in complete lattices for statements used in both complete and conditionally complete lattices.

### `beta_reduce`
- **Syntax Reference:** `[Mathlib.Tactic.betaReduceStx]`
- **Description:** Completely beta reduces a location, substituting arguments into lambda expressions. Also available in `conv` mode.

### `bicategory`
- **Syntax Reference:** `[Mathlib.Tactic.Bicategory.tacticBicategory]`
- **Description:** Solves equations in bicategories differing only by structural morphisms using the coherence theorem.

### `bicategory_coherence`
- **Syntax Reference:** `[Mathlib.Tactic.BicategoryCoherence.tacticBicategory_coherence]`, `[Mathlib.Tactic.Bicategory.tacticBicategory_coherence]`
- **Description:** Closes goals of the form `η = θ` where `η` and `θ` are 2-isomorphisms of associators, unitors, and identities. Use `pure_coherence` instead.

### `bicategory_nf`
- **Syntax Reference:** `[Mathlib.Tactic.Bicategory.tacticBicategory_nf]`
- **Description:** Normalizes both sides of an equality in a bicategory.

### `borelize`
- **Syntax Reference:** `[Mathlib.Tactic.Borelize.tacticBorelize___]`
- **Description:** Adjusts `MeasurableSpace` instances to `borel α` based on existing assumptions, adding `BorelSpace` instances as needed.

### `bound`
- **Syntax Reference:** `[«tacticBound[_]»]`
- **Description:** Proves inequalities via recursion on expression structure using `@[bound]` and `@[bound_forward]` lemmas, local hypotheses, and optional additional hypotheses.

### `bv_check`
- **Syntax Reference:** `[Lean.Parser.Tactic.bvCheck]`
- **Description:** Like `bv_decide` but uses a pre-stored LRAT proof file instead of calling a SAT solver, e.g., `bv_check "proof.lrat"`.

### `bv_decide`
- **Syntax Reference:** `[Lean.Parser.Tactic.bvDecide]`, `[Lean.Parser.Tactic.bvDecideMacro]`
- **Description:** Closes `BitVec` and `Bool` goals using an external SAT solver, verifying the proof in Lean. Limited to QF_BV-like goals and structures. Provides counterexamples on failure.

### `bv_decide?`
- **Syntax Reference:** `[Lean.Parser.Tactic.bvTraceMacro]`, `[Lean.Parser.Tactic.bvTrace]`
- **Description:** Suggests a proof script for `bv_decide` to cache LRAT proofs.

### `bv_normalize`
- **Syntax Reference:** `[Lean.Parser.Tactic.bvNormalize]`, `[Lean.Parser.Tactic.bvNormalizeMacro]`
- **Description:** Runs `bv_decide`’s normalization procedure to solve basic `BitVec` goals.

### `bv_omega`
- **Syntax Reference:** `[Lean.Parser.Tactic.tacticBv_omega]`
- **Description:** Adapts `omega` for `BitVec` by converting to `Nat` statements with `bitvec_to_nat`.

### `by_cases`
- **Syntax Reference:** `[«tacticBy_cases_:_»]`
- **Description:** Splits the goal into two cases: `h : p` and `h : ¬ p`.

### `by_contra`
- **Syntax Reference:** `[Batteries.Tactic.byContra]`
- **Description:** Proves `⊢ p` by contradiction, introducing `h : ¬p` and proving `False`. Handles decidable cases and negation normalization.

### `by_contra!`
- **Syntax Reference:** `[byContra!]`
- **Description:** Reduces `⊢ p` to proving `False` with `h : ¬ p`, normalizing negations with `push_neg`. Uses classical reasoning.

### `calc`
- **Syntax Reference:** `[Lean.calcTactic]`
- **Description:** Performs step-wise reasoning over transitive relations, e.g., `calc a = b := pab ... y = z := pyz`.

### `rwa`
- **Syntax Reference:** `[Lean.Parser.Tactic.tacticRwa__]`
- **Description:** Short-hand for `rw; assumption`.

### `saturate`
- **Syntax Reference:** `[Aesop.Frontend.tacticSaturate____]`
- **Description:** (No detailed description provided in the document.)

### `saturate?`
- **Syntax Reference:** `[Aesop.Frontend.tacticSaturate?____]`
- **Description:** (No detailed description provided in the document.)

### `says`
- **Syntax Reference:** `[Mathlib.Tactic.Says.says]`
- **Description:** Enhances a tactic `X` producing "Try this: Y" with "Try this: X says Y", then runs `Y` after replacement. Verifiable with `set_option says.verify true`.

### `set`
- **Syntax Reference:** `[Mathlib.Tactic.setTactic]`
- **Description:** (No detailed description provided in the document.)

### `set!`
- **Syntax Reference:** `[Mathlib.Tactic.tacticSet!_]`
- **Description:** (No detailed description provided in the document.)

### `set_option`
- **Syntax Reference:** `[Lean.Parser.Tactic.set_option]`
- **Description:** Temporarily sets an option for a tactic block, e.g., `set_option opt val in tacs`.

### `show`
- **Syntax Reference:** `[Lean.Parser.Tactic.tacticShow_]`
- **Description:** Unifies the first matching goal with a term `t`, making it the main goal and replacing the target with the unified `t`.

### `show_term`
- **Syntax Reference:** `[Lean.Parser.Tactic.showTerm]`
- **Description:** Runs a tactic and prints the generated term, e.g., "exact X Y Z" or "refine X ?_ Z".

### `simp`
- **Syntax Reference:** `[Lean.Parser.Tactic.simp]`
- **Description:** Simplifies the goal or hypotheses using `[simp]` lemmas and optional expressions, with variants like `simp only`, `simp at`, and `simp [*]`.

### `simp!`
- **Syntax Reference:** `[Lean.Parser.Tactic.simpAutoUnfold]`
- **Description:** `simp` with `autoUnfold := true`, rewriting with all equation lemmas for partial evaluation.

### `simp?`
- **Syntax Reference:** `[Lean.Parser.Tactic.simpTrace]`
- **Description:** Like `simp` but suggests an equivalent `simp only` call to close the goal, reducing simp set size.

### `simp?!`
- **Syntax Reference:** `[Lean.Parser.Tactic.tacticSimp?!_]`
- **Description:** Combines `simp?` and `simp!` behaviors.

### `simp_all`
- **Syntax Reference:** `[Lean.Parser.Tactic.simpAll]`
- **Description:** Repeatedly simplifies all propositional hypotheses and the target until no further simplification is possible.

### `simp_all!`
- **Syntax Reference:** `[Lean.Parser.Tactic.simpAllAutoUnfold]`
- **Description:** `simp_all` with `autoUnfold := true`.

### `simp_all?`
- **Syntax Reference:** `[Lean.Parser.Tactic.simpAllTrace]`
- **Description:** `simp_all` with suggestion of an equivalent `simp only` call.

### `simp_all?!`
- **Syntax Reference:** `[Lean.Parser.Tactic.tacticSimp_all?!_]`
- **Description:** Combines `simp_all?` and `simp_all!` behaviors.

### `simp_all_arith`
- **Syntax Reference:** `[Lean.Parser.Tactic.simpAllArith]`
- **Description:** Deprecated shorthand for `simp_all +arith +decide`. No longer needs `+decide` due to simprocs.

### `simp_all_arith!`
- **Syntax Reference:** `[Lean.Parser.Tactic.simpAllArithBang]`
- **Description:** Deprecated shorthand for `simp_all! +arith +decide`.

### `simp_arith`
- **Syntax Reference:** `[Lean.Parser.Tactic.simpArith]`
- **Description:** Deprecated shorthand for `simp +arith +decide`.

### `simp_arith!`
- **Syntax Reference:** `[Lean.Parser.Tactic.simpArithBang]`
- **Description:** Deprecated shorthand for `simp! +arith +decide`.

### `simp_intro`
- **Syntax Reference:** `[Mathlib.Tactic.«tacticSimp_intro_____..Only_»]`
- **Description:** Combines `simp` and `intro`, simplifying variable types as they are introduced and using them to simplify subsequent arguments and the goal.

### `simp_rw`
- **Syntax Reference:** `[Mathlib.Tactic.tacticSimp_rw___]`
- **Description:** Mixes `simp` and `rw`, applying rewrite rules in order and repeatedly under binders like `∀`, `∃`, and `fun`.

### `simp_wf`
- **Syntax Reference:** `[tacticSimp_wf]`
- **Description:** Unfolds definitions in well-founded relations, now obsolete since Lean 4.12 unfolds them automatically.

### `simpa`
- **Syntax Reference:** `[Lean.Parser.Tactic.simpa]`
- **Description:** A finishing tactic modifying `simp`, either using an expression (`simpa using e`) or a hypothesis `this` to close the goal after simplification.

### `simpa!`
- **Syntax Reference:** `[Lean.Parser.Tactic.tacticSimpa!_]`
- **Description:** `simpa` with `autoUnfold := true`.

### `simpa?`
- **Syntax Reference:** `[Lean.Parser.Tactic.tacticSimpa?_]`
- **Description:** `simpa` with suggestion of an equivalent `simp only` call.

### `simpa?!`
- **Syntax Reference:** `[Lean.Parser.Tactic.tacticSimpa?!_]`
- **Description:** Combines `simpa?` and `simpa!` behaviors.

### `sizeOf_list_dec`
- **Syntax Reference:** `[List.tacticSizeOf_list_dec]`
- **Description:** Proves `sizeOf a < sizeOf as` when `a ∈ as` for well-founded recursions over nested inductives.

### `skip`
- **Syntax Reference:** `[Lean.Parser.Tactic.skip]`
- **Description:** Does nothing.

### `sleep`
- **Syntax Reference:** `[Lean.Parser.Tactic.sleep]`
- **Description:** Sleeps for a specified number of milliseconds, used for debugging.

### `slice_lhs`
- **Syntax Reference:** `[sliceLHS]`
- **Description:** Zooms to the left-hand side, adjusts categorical composition with associativity, and invokes a tactic on specified morphisms.

### `slice_rhs`
- **Syntax Reference:** `[sliceRHS]`
- **Description:** Zooms to the right-hand side, adjusts categorical composition, and invokes a tactic on specified morphisms.

### `smul_tac`
- **Syntax Reference:** `[RatFunc.tacticSmul_tac]`
- **Description:** Solves equations for `RatFunc K` by applying `RatFunc.induction_on`.

### `solve`
- **Syntax Reference:** `[Lean.solveTactic]`
- **Description:** Succeeds only if one of the given tactics solves the current goal, similar to `first`.

### `solve_by_elim`
- **Syntax Reference:** `[Lean.Parser.Tactic.solveByElim]`
- **Description:** Repeatedly applies assumptions to solve the goal and subgoals up to a specified depth, with backtracking and customizable assumptions.

### `sorry`
- **Syntax Reference:** `[Lean.Parser.Tactic.tacticSorry]`
- **Description:** Closes the goal with a placeholder, intended for incomplete proofs, triggering a warning.

### `sorry_if_sorry`
- **Syntax Reference:** `[CategoryTheory.sorryIfSorry]`
- **Description:** Closes the goal with `sorry` if its type contains `sorry`, failing otherwise.

### `specialize`
- **Syntax Reference:** `[Lean.Parser.Tactic.specialize]`
- **Description:** Instantiates premises of a hypothesis with concrete terms, adding a new hypothesis and clearing the old one if possible.

### `specialize_all`
- **Syntax Reference:** `[Mathlib.Tactic.TautoSet.specialize_all]`
- **Description:** Runs `specialize h x` on all applicable hypotheses.

### `split`
- **Syntax Reference:** `[Lean.Parser.Tactic.split]`
- **Description:** Breaks nested `if-then-else` and `match` expressions into separate goals, e.g., splitting `if n = 0 then Q else R`.

### `split_ands`
- **Syntax Reference:** `[Batteries.Tactic.tacticSplit_ands]`
- **Description:** Applies `And.intro` until no progress is made.

### `split_ifs`
- **Syntax Reference:** `[Mathlib.Tactic.splitIfs]`
- **Description:** Splits all `if-then-else` expressions into multiple goals, optionally at specified locations with custom hypothesis names.

### `stop`
- **Syntax Reference:** `[Lean.Parser.Tactic.tacticStop_]`
- **Description:** Discards the rest of a proof with `repeat sorry`, useful for focusing on earlier parts.

### `subsingleton`
- **Syntax Reference:** `[Mathlib.Tactic.subsingletonStx]`
- **Description:** Proves equalities or heterogeneous equalities using subsingleton properties, running `intros` first and supporting additional instances.

### `subst`
- **Syntax Reference:** `[Lean.Parser.Tactic.subst]`
- **Description:** Substitutes variables with equal terms based on hypotheses, handling nested equalities.

### `subst_eqs`
- **Syntax Reference:** `[Lean.Parser.Tactic.substEqs]`
- **Description:** Repeatedly substitutes according to equality hypotheses until no further progress.

### `subst_vars`
- **Syntax Reference:** `[Lean.Parser.Tactic.substVars]`
- **Description:** Applies `subst` to all hypotheses of the form `x = t` or `t = x`.

### `substs`
- **Syntax Reference:** `[Mathlib.Tactic.Substs.substs]`
- **Description:** Applies `subst` to given hypotheses from left to right.

### `success_if_fail_with_msg`
- **Syntax Reference:** `[Mathlib.Tactic.successIfFailWithMsg]`
- **Description:** Succeeds only if a tactic fails with a specified message.

### `suffices`
- **Syntax Reference:** `[Lean.Parser.Tactic.tacticSuffices_]`, `[Mathlib.Tactic.tacticSuffices_]`
- **Description:** Replaces the goal with a new one, proving the original using an expression or tactic, optionally naming the hypothesis.

### `suggest_premises`
- **Syntax Reference:** `[Lean.Parser.Tactic.suggestPremises]`
- **Description:** Suggests premises for the goal using the registered premise selector, ordered by confidence.

### `swap`
- **Syntax Reference:** `[Batteries.Tactic.tacticSwap]`
- **Description:** Interchanges the 1st and 2nd goals, equivalent to `pick_goal 2`.

### `swap_var`
- **Syntax Reference:** `[Mathlib.Tactic.«tacticSwap_var__,,»]`
- **Description:** Swaps variable names in hypotheses and the goal according to specified rules.

### `symm`
- **Syntax Reference:** `[Lean.Parser.Tactic.symm]`
- **Description:** Reverses a symmetric relation in the goal or a hypothesis using `[symm]` lemmas.

### `symm_saturate`
- **Syntax Reference:** `[Lean.Parser.Tactic.symmSaturate]`
- **Description:** Adds symmetric versions of hypotheses with `@[symm]` lemmas.

### `tauto`
- **Syntax Reference:** `[Mathlib.Tactic.Tauto.tauto]`
- **Description:** Breaks down logical assumptions and splits goals until solvable by `reflexivity` or `solve_by_elim`, using classical reasoning.

### `tauto_set`
- **Syntax Reference:** `[Mathlib.Tactic.TautoSet.tacticTauto_set]`
- **Description:** Proves tautologies involving set operations (`⊆`, `=`, ∪, ∩, \, ᶜ`) and unfolds `Disjoint` and `symmDiff`.

### `tfae_finish`
- **Syntax Reference:** `[Mathlib.Tactic.TFAE.tfaeFinish]`
- **Description:** Closes `TFAE [P₁, P₂, ...]` goals once sufficient `Pᵢ → Pⱼ` or `Pᵢ ↔ Pⱼ` hypotheses are introduced.

### `tfae_have`
- **Syntax Reference:** `[Mathlib.Tactic.TFAE.tfaeHave]`, `[Mathlib.Tactic.TFAE.tfaeHave']`
- **Description:** Introduces hypotheses like `Pᵢ → Pⱼ` for `TFAE` proofs, supporting naming and matching. Deprecated goal-style syntax requires `:=`.

### `toFinite_tac`
- **Syntax Reference:** `[Set.tacticToFinite_tac]`
- **Description:** Applies `Set.toFinite` to synthesize `Set.Finite` terms in auto-params.

### `to_encard_tac`
- **Syntax Reference:** `[Set.tacticTo_encard_tac]`
- **Description:** Transfers `encard` proofs to corresponding `card` statements.

### `trace`
- **Syntax Reference:** `[Lean.Parser.Tactic.trace]`, `[Lean.Parser.Tactic.traceMessage]`
- **Description:** Evaluates a term to a string and prints it as a trace message or displays a specified message.

### `trace_state`
- **Syntax Reference:** `[Lean.Parser.Tactic.traceState]`
- **Description:** Displays the current tactic state in the info view.

### `trans`
- **Syntax Reference:** `[Batteries.Tactic.tacticTrans___]`
- **Description:** Applies transitivity to a goal with a transitive relation, splitting into two subgoals or using a metavariable.

### `transitivity`
- **Syntax Reference:** `[Batteries.Tactic.tacticTransitivity___]`
- **Description:** Synonym for `trans`.

### `triv`
- **Syntax Reference:** `[Batteries.Tactic.triv]`
- **Description:** Deprecated variant of `trivial`.

### `trivial`
- **Syntax Reference:** `[Lean.Parser.Tactic.tacticTrivial]`
- **Description:** Tries simple tactics like `rfl` and `contradiction` to close the goal, extensible via `macro_rules`.

### `try`
- **Syntax Reference:** `[Lean.Parser.Tactic.tacticTry_]`
- **Description:** Runs a tactic and succeeds even if it fails.

### `try?`
- **Syntax Reference:** `[Lean.Parser.Tactic.tryTrace]`
- **Description:** (No detailed description provided, internal use for `try?` implementation.)

### `try_suggestions`
- **Syntax Reference:** `[Lean.Parser.Tactic.tryResult]`
- **Description:** Internal helper for `evalSuggest` in `try?`.

### `try_this`
- **Syntax Reference:** `[Mathlib.Tactic.tacticTry_this__]`
- **Description:** Suggests and executes a tactic with "Try this: <tac>".

### `type_check`
- **Syntax Reference:** `[tacticType_check_]`
- **Description:** Type checks an expression and traces its type.

### `unfold`
- **Syntax Reference:** `[Lean.Parser.Tactic.unfold]`
- **Description:** Unfolds definitions in the target or hypotheses, using unfolding lemmas for recursive definitions.

### `unfold?`
- **Syntax Reference:** `[Mathlib.Tactic.InteractiveUnfold.tacticUnfold?]`
- **Description:** Suggests definitional unfoldings for a selected expression, simplifying with `whnfCore` and hiding default instance unfolds.

### `unfold_let`
- **Syntax Reference:** `[Mathlib.Tactic.unfoldLetStx]`
- **Description:** Subsumed by `unfold`, performs zeta reduction on local definitions. Also available as `zeta` in `conv` mode.

### `unfold_projs`
- **Syntax Reference:** `[Mathlib.Tactic.unfoldProjsStx]`
- **Description:** Unfolds class instance projections at a location, also available in `conv` mode.

### `unhygienic`
- **Syntax Reference:** `[Lean.Parser.Tactic.tacticUnhygienic_]`
- **Description:** Runs tactics with name hygiene disabled, making normally inaccessible names regular variables (use cautiously).

### `uniqueDiffWithinAt_Ici_Iic_univ`
- **Syntax Reference:** `[intervalIntegral.tacticUniqueDiffWithinAt_Ici_Iic_univ]`
- **Description:** Closes goals of the form `UniqueDiffWithinAt ℝ s a` where `s` is `Iic a`, `Ici a`, or `univ`.

### `unit_interval`
- **Syntax Reference:** `[Tactic.Interactive.tacticUnit_interval]`
- **Description:** Solves inequalities like `0 ≤ ↑x` and `↑x ≤ 1` for `x : I`.

### `unreachable!`
- **Syntax Reference:** `[Batteries.Tactic.unreachable]`
- **Description:** Causes a compile-time panic, intended for asserting a tactic is never executed in tests.

### `use`
- **Syntax Reference:** `[Mathlib.Tactic.useSyntax]`
- **Description:** Similar to `exists`, refines with multiple terms and discharges goals with a configurable tactic, e.g., `use 42, 42`.

### `use!`
- **Syntax Reference:** `[Mathlib.Tactic.«tacticUse!___,,»]`
- **Description:** Like `use` but applies constructors everywhere, flattening nested structures.

### `use_discharger`
- **Syntax Reference:** `[Mathlib.Tactic.tacticUse_discharger]`
- **Description:** Default discharger for `use` and `use!`, similar to `trivial` but avoids `contradiction` or `decide`.

### `use_finite_instance`
- **Syntax Reference:** `[tacticUse_finite_instance]`
- **Description:** (No detailed description provided in the document.)

### `volume_tac`
- **Syntax Reference:** `[MeasureTheory.tacticVolume_tac]`
- **Description:** Uses `exact volume` in auto-param arguments.

### `wait_for_unblock_async`
- **Syntax Reference:** `[Lean.Server.Test.Cancel.tacticWait_for_unblock_async]`
- **Description:** Waits for an `unblock` call in a subsequent document version, checking for cancellation.

### `whisker_simps`
- **Syntax Reference:** `[Mathlib.Tactic.BicategoryCoherence.whisker_simps]`
- **Description:** Simp lemmas for rewriting 2-morphisms into normal form.

### `whnf`
- **Syntax Reference:** `[Mathlib.Tactic.tacticWhnf__]`
- **Description:** Reduces a location to weak-head normal form, also available in `conv` mode.

### `with_panel_widgets`
- **Syntax Reference:** `[ProofWidgets.withPanelWidgetsTacticStx]`
- **Description:** Displays selected panel widgets alongside the tactic state in a proof.

### `with_reducible`
- **Syntax Reference:** `[Lean.Parser.Tactic.withReducible]`
- **Description:** Executes tactics with reducible transparency, unfolding only `[reducible]` definitions.

### `with_reducible_and_instances`
- **Syntax Reference:** `[Lean.Parser.Tactic.withReducibleAndInstances]`
- **Description:** Executes tactics with `.instances` transparency, unfolding `[reducible]` and type class instances.

### `with_unfolding_all`
- **Syntax Reference:** `[Lean.Parser.Tactic.withUnfoldingAll]`
- **Description:** Executes tactics with `.all` transparency, unfolding all non-opaque definitions.

### `wlog`
- **Syntax Reference:** `[Mathlib.Tactic.wlog]`
- **Description:** Adds an assumption `h : P` to the main goal and a side goal reducing `¬ P` to `P`, often used with symmetry and generalization.

### `zify`
- **Syntax Reference:** `[Mathlib.Tactic.Zify.zify]`
- **Description:** Shifts `Nat` propositions to `Int` for better subtraction handling, using `@[zify_simps]` and `push_cast`.

### `·`
- **Syntax Reference:** `[Lean.cdot]`
- **Description:** Focuses on the main goal and tries to solve it with a tactic, failing otherwise.

---

This list is generated from the provided document and reflects tactics available as of March 24, 2025. For full details, refer to the original Lean documentation.
