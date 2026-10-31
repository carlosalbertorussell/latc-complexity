import LatcComplexity.Valiant.OneCall

/-!
# Axiom audit of the Valiant files

Every theorem of `LatcComplexity/Valiant/` should depend only on `propext`, `Classical.choice`
and `Quot.sound`.
-/

open Latc.PaperD.Valiant

-- Gadget.lean: polynomial time
#print axioms vv_polyTime
#print axioms vv_polyTime'
#print axioms cv_polyTime
#print axioms cv_polyTime'
#print axioms lv_polyTime
#print axioms lv_polyTime'
#print axioms edge_polyTime
#print axioms edge_polyTime'
#print axioms verts_polyTime
#print axioms leafClauses_polyTime
#print axioms graphClauses_polyTime
#print axioms psi_polyTime
#print axioms toMonotone_polyTime
#print axioms numClauses_polyTime
#print axioms numOcc_polyTime
#print axioms leaves_polyTime
#print axioms expK_polyTime
#print axioms expN_polyTime
#print axioms post_polyTime

-- Counting.lean: codes, independent sets, maximum independent sets
#print axioms vv_mod
#print axioms cv_mod
#print axioms lv_mod
#print axioms vv_ne_cv
#print axioms lv_ne_vv
#print axioms lv_ne_cv
#print axioms vv_inj
#print axioms lv_inj
#print axioms cv_eq
#print axioms occ_ext
#print axioms cv_inj
#print axioms mem_verts
#print axioms mem_graphClauses
#print axioms mem_leafClauses
#print axioms eval_edge
#print axioms mem_edge
#print axioms eval_edge_not_mem
#print axioms indep_iff
#print axioms part_vv
#print axioms part_cv
#print axioms part_injOn
#print axioms part_mapsTo
#print axioms card_le_of_indep
#print axioms firstTrue_iff
#print axioms literal_eval_iff
#print axioms vv_mem_setOf
#print axioms cv_mem_setOf
#print axioms setOf_subset
#print axioms firstTrue_unique
#print axioms exists_firstTrue
#print axioms indep_setOf
#print axioms card_disjSum_parts
#print axioms card_setOf
#print axioms exists_of_indep
#print axioms setOf_eq_iff
#print axioms mem_falseSet
#print axioms falseSet_subset
#print axioms modelCount_eq_card

-- Pendant.lean: the pendant leaves
#print axioms mem_vars_iff
#print axioms graph_vars_mem
#print axioms mem_vars_psi
#print axioms lv_not_mem_verts
#print axioms eval_append
#print axioms graph_eval_iff
#print axioms lv_div
#print axioms card_leaves
#print axioms modelCount_psi

-- OneCall.lean: the digit, the reduction, Valiant's theorem and the corollaries
#print axioms digit
#print axioms verts_toFinset
#print axioms card_V0
#print axioms card_falseSet
#print axioms card_true
#print axioms modelCount_le
#print axioms modelCount_eq_post
#print axioms monotone2B_psi
#print axioms sharpSAT_eq_post
#print axioms sharpSAT_oneCallReducible
#print axioms ParsimoniousReducible.trans_oneCall
#print axioms sharpMonotone2SAT_oneCallSharpPHard
#print axioms countValidMonotone2_sharpPComplete_oneCall
#print axioms countValidMonotone2_sharpPComplete_oneCall_unary
