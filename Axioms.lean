/-
Machine-checked attestation of the axiom profile. `lake env lean Axioms.lean`
fails if any proved lemma acquires an axiom dependency, or if the companion
theorems stop depending on `sorryAx` — that is, if the single deliberate `sorry`
silently moves or multiplies. Run in CI.
-/
import LambdaAdicSlice.Companions

/-- info: 'LambdaAdicSlice.charpoly_eq_of_isConj_gl' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LambdaAdicSlice.charpoly_eq_of_isConj_gl

/-- info: 'LambdaAdicSlice.charpoly_eq_of_isConj' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LambdaAdicSlice.charpoly_eq_of_isConj

/-- info: 'LambdaAdicSlice.isFrobAt_conj' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LambdaAdicSlice.isFrobAt_conj

/-- info: 'LambdaAdicSlice.toHom_eq_of_isArithFrobAt' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LambdaAdicSlice.toHom_eq_of_isArithFrobAt

/-- info: 'LambdaAdicSlice.charpoly_eq_of_isArithFrobAt' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LambdaAdicSlice.charpoly_eq_of_isArithFrobAt

/-- info: 'LambdaAdicSlice.exists_companion' depends on axioms:
[propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LambdaAdicSlice.exists_companion

/-- info: 'LambdaAdicSlice.exists_companion_family' depends on axioms:
[propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LambdaAdicSlice.exists_companion_family
