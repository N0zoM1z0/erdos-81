import Erdos81

/-!
# Kernel-assumption audit

These commands display the assumptions of the principal proved declarations.
The project introduces no custom axioms.  Mathlib may report Lean's standard
logical primitives (for example quotient soundness or choice) where a theorem
uses classical finite-set reasoning.
-/

#check Erdos81.IsChordal
#check Erdos81.CliquePartition
#check Erdos81.Erdos81Statement
#check Erdos81.EventualSharpUpperBound
#check Erdos81.eventualSharpUpperBound_implies_erdos81

#print axioms Erdos81.Arithmetic.square_identity
#print axioms Erdos81.Arithmetic.first_entry_numerics
#print axioms Erdos81.Arithmetic.second_branch_square_identity
#print axioms Erdos81.Arithmetic.far_case_closure
#print axioms Erdos81.Chordal.commonNeighbors_isClique_of_chordal
#print axioms Erdos81.Copying.opposite_copy_edge_count
#print axioms Erdos81.Copying.simplicial_target_of_simplicial_source
#print axioms Erdos81.Copying.chordal_replaceVertex_of_simplicial_source
#print axioms Erdos81.DiscreteConvexity.monotone_to_right_endpoint
#print axioms Erdos81.DiscreteConvexity.potential_copy_inequality
#print axioms Erdos81.FiniteLP.weak_duality
#print axioms Erdos81.FirstEntry.barrier
#print axioms Erdos81.FirstEntry.inverse_order_lt_quarter_radius
#print axioms Erdos81.LocalStability.defect_sum_le_nine_delta
#print axioms Erdos81.LocalStability.root_displacement_squared
#print axioms Erdos81.LocalStability.nat_le_sharpBound_of_le_Q
#print axioms Erdos81.MixedModel.weak_duality
#print axioms Erdos81.RootArithmetic.ceil_seven_quarters_le_nine_fifths
#print axioms Erdos81.RootArithmetic.final_host_margin_nonnegative
#print axioms Erdos81.SharpBound.floor_Q_eq_sharpBound
#print axioms Erdos81.SplitDual.exact_minimum
#print axioms Erdos81.SplitDual.potential_three_branch_formula
#print axioms Erdos81.pairPartition_size_le_square
#print axioms Erdos81.eventualSharpUpperBound_implies_erdos81
