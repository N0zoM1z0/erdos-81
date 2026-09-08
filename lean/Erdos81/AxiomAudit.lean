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
#check Erdos81.ExternalInputs.VizingInput
#check Erdos81.ExternalInputs.HaggkvistJanssenInput
#check Erdos81.ExternalInputs.PackingTransferInput
#check Erdos81.ExternalInputs.Inputs

#print axioms Erdos81.Arithmetic.square_identity
#print axioms Erdos81.Arithmetic.first_entry_numerics
#print axioms Erdos81.Arithmetic.second_branch_square_identity
#print axioms Erdos81.Arithmetic.far_case_closure
#print axioms Erdos81.Chordal.commonNeighbors_isClique_of_chordal
#print axioms Erdos81.Chordal.induce_isChordal
#print axioms Erdos81.Chordal.root_nonadjacency_degree_bound
#print axioms Erdos81.ChordalWalk.geodesic_not_adj_of_gap
#print axioms Erdos81.ChordalWalk.append_reverse_isCycle
#print axioms Erdos81.ChordalWalk.inducedCycleEmbedding
#print axioms Erdos81.ChordalWalk.inducedCycleEmbedding_of_two_arcs
#print axioms Erdos81.CliquePartitionCounting.sum_choose_eq_card_edges
#print axioms Erdos81.Separator.exists_minimal_separator
#print axioms Erdos81.Separator.exists_neighbor_in_component
#print axioms Erdos81.ChordalSeparator.exists_component_arc
#print axioms Erdos81.ChordalSeparator.minimal_separator_isClique
#print axioms Erdos81.Dirac.complete_or_two_simplicial
#print axioms Erdos81.Dirac.exists_simplicial
#print axioms Erdos81.Copying.opposite_copy_edge_count
#print axioms Erdos81.Copying.collapseHom
#print axioms Erdos81.Copying.card_finset_image_of_isClique
#print axioms Erdos81.Copying.simplicial_target_of_simplicial_source
#print axioms Erdos81.Copying.chordal_replaceVertex_of_simplicial_source
#print axioms Erdos81.CopyCover.pullback_incidence_sum
#print axioms Erdos81.CopyCover.pullbackCover
#print axioms Erdos81.CopyCover.coverValue_opposite_pullbacks
#print axioms Erdos81.CopyCover.potential_opposite_copy_inequality
#print axioms Erdos81.DiscreteConvexity.monotone_to_right_endpoint
#print axioms Erdos81.DiscreteConvexity.potential_copy_inequality
#print axioms Erdos81.EditDistance.edgeEditDistance_triangle
#print axioms Erdos81.EditDistance.edgeEditDistance_replaceVertex_le
#print axioms Erdos81.EditDistance.splitEditDistance_replaceVertex_dist_le
#print axioms Erdos81.FiniteLP.weak_duality
#print axioms Erdos81.FirstEntry.barrier
#print axioms Erdos81.FirstEntry.inverse_order_lt_quarter_radius
#print axioms Erdos81.FirstEntryGraph.normalized_movement_of_dist_le
#print axioms Erdos81.FirstEntryGraph.copyPath_barrier_at_manuscript_scale
#print axioms Erdos81.IntegralFractional.toFractional
#print axioms Erdos81.IntegralFractional.packingValue_toFractional
#print axioms Erdos81.IntegralFractional.potential_le_size_of_orderAtMost_three
#print axioms Erdos81.IntegralPacking.size_toCliquePartition
#print axioms Erdos81.IntegralPacking.gain_ofCliquePartition
#print axioms Erdos81.IntegralPacking.isIntegralOptimum_iff_isRestrictedPartitionMinimum
#print axioms Erdos81.IntegralPacking.exists_integralOptimum_and_restrictedPartitionMinimum
#print axioms Erdos81.LocalStability.defect_sum_le_nine_delta
#print axioms Erdos81.LocalStability.root_displacement_squared
#print axioms Erdos81.LocalStability.manuscript_contraction_numerics
#print axioms Erdos81.LocalStability.nat_le_sharpBound_of_le_Q
#print axioms Erdos81.LocalRoot.exists_initialRoot
#print axioms Erdos81.LocalRootArithmetic.initialRoot_numerics
#print axioms Erdos81.LocalRootArithmetic.cast_dist_div_three_le_abs_displacement
#print axioms Erdos81.LocalRegularization.exists_strict_partition_of_split_close
#print axioms Erdos81.LocalRegularization.exists_partition_le_sharpBound_of_split_close
#print axioms Erdos81.LocalPotential.near_extremal_split_contraction
#print axioms Erdos81.MixedModel.weak_duality
#print axioms Erdos81.PerfectElimination.card_edgeFinset_eq_sum_laterNeighbors
#print axioms Erdos81.PerfectElimination.isChordal_of_peo
#print axioms Erdos81.PerfectElimination.isChordal_of_hasPEO
#print axioms Erdos81.PerfectElimination.edge_bound_of_peo
#print axioms Erdos81.PerfectElimination.edge_bound_of_hasPEO
#print axioms Erdos81.PerfectElimination.card_edges_add_card_complement
#print axioms Erdos81.PerfectElimination.complement_edge_bound_of_peo
#print axioms Erdos81.PerfectElimination.complement_edge_bound_of_hasPEO
#print axioms Erdos81.PEOExistence.exists_elimination_list
#print axioms Erdos81.PEOExistence.exists_elimination_list_ending_clique
#print axioms Erdos81.PEOExistence.hasPEO_of_chordal
#print axioms Erdos81.PEOExistence.isChordal_iff_hasPEO
#print axioms Erdos81.PEOExistence.edge_bound_of_chordal
#print axioms Erdos81.PEOExistence.complement_edge_bound_of_chordal
#print axioms Erdos81.RootArithmetic.ceil_seven_quarters_le_nine_fifths
#print axioms Erdos81.RootArithmetic.final_host_margin_nonnegative
#print axioms Erdos81.RootDistance.exists_resized_completeSplitGraph
#print axioms Erdos81.RootDistance.splitEditDistance_le_rootDefects_add_roles
#print axioms Erdos81.RootDemotion.outsideEdges_retained_le
#print axioms Erdos81.RootOptimization.optimizedRoot_bounds
#print axioms Erdos81.RootRegularization.exists_strict_partition
#print axioms Erdos81.RootRegularization.exists_regularized_strict_partition
#print axioms Erdos81.RootedGraph.edgeFinset_partition
#print axioms Erdos81.RootedGraph.edge_count_identity
#print axioms Erdos81.SharpBound.floor_Q_eq_sharpBound
#print axioms Erdos81.SplitDual.exact_minimum
#print axioms Erdos81.SplitDual.potential_three_branch_formula
#print axioms Erdos81.TrianglePacking.exists_partition
#print axioms Erdos81.pairPartition_size_le_square
#print axioms Erdos81.eventualSharpUpperBound_implies_erdos81
