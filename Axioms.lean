/-
Machine-checked attestation of the axiom profile. `lake env lean Axioms.lean`
fails if any proved lemma acquires an axiom dependency or if either companion
theorem's axiom set changes. It pins the set of axiom names, not the number or
location of `sorry` terms; the source-level line count in CI covers
those, for `sorry` written on its own line. Run in
CI.
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
