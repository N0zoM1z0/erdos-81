import Erdos81

/-!
# Kernel-assumption audit

These commands display the assumptions of the principal proved declarations.
The project introduces no custom axioms.  Mathlib may report Lean's standard
logical primitives (for example quotient soundness or choice) where a theorem
uses classical finite-set reasoning.
-/

#print axioms Erdos81.Arithmetic.square_identity
#print axioms Erdos81.Arithmetic.first_entry_numerics
#print axioms Erdos81.Arithmetic.far_case_closure
#print axioms Erdos81.pairPartition_size_le_square
#print axioms Erdos81.eventualSharpUpperBound_implies_erdos81
