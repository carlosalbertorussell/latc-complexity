import LatcComplexity.Bridge
import LatcComplexity.General
import LatcComplexity.Adequacy
import LatcComplexity.Counting
import LatcComplexity.CountingGeneral
import LatcComplexity.Monotone
import LatcComplexity.Binary
import LatcComplexity.Tractable
import LatcComplexity.ExplicitDegree

/-! Axiom audit: each theorem should depend only on `propext`, `Classical.choice` and
`Quot.sound`. -/

-- Boolean domains (`LatcComplexity/Bridge.lean`)
#print axioms Latc.PaperD.holdsAll_eq_eval
#print axioms Latc.PaperD.satisfiable_decode_iff
#print axioms Latc.PaperD.fromSAT_polyTime
#print axioms Latc.PaperD.SAT_reduces
#print axioms Latc.PaperD.MissingNonempty_npHard
#print axioms Latc.PaperD.Complete_coNPHard
#print axioms Latc.PaperD.tupleOf_polyTime
#print axioms Latc.PaperD.verifier_polyTime
#print axioms Latc.PaperD.isVerifier
#print axioms Latc.PaperD.MissingNonempty_mem_NP
#print axioms Latc.PaperD.MissingNonempty_npComplete
#print axioms Latc.PaperD.Complete_coNPComplete
#print axioms Latc.PaperD.countMissing_fromSAT
#print axioms Latc.PaperD.countMissing_sharpPHard

-- General finite domains (`LatcComplexity/General.lean`)
#print axioms Latc.PaperD.General.inDomainsB_iff
#print axioms Latc.PaperD.General.condHoldsB_iff
#print axioms Latc.PaperD.General.check_iff
#print axioms Latc.PaperD.General.check_polyTime
#print axioms Latc.PaperD.General.length_encList_le_of_inDomains
#print axioms Latc.PaperD.General.MissingNonempty_mem_NP
#print axioms Latc.PaperD.General.fromSAT_polyTime
#print axioms Latc.PaperD.General.satisfiable_iff
#print axioms Latc.PaperD.General.SAT_reduces
#print axioms Latc.PaperD.General.MissingNonempty_npHard
#print axioms Latc.PaperD.General.MissingNonempty_npComplete
#print axioms Latc.PaperD.General.Complete_coNPComplete

-- Adequacy to latc-check's `Finset` model (`LatcComplexity/Adequacy.lean`)
#print axioms Latc.PaperD.General.Inst.toList_injective
#print axioms Latc.PaperD.General.Inst.inDomains_toList
#print axioms Latc.PaperD.General.Inst.exists_toList_eq
#print axioms Latc.PaperD.General.con_cond_iff
#print axioms Latc.PaperD.General.con_iff
#print axioms Latc.PaperD.General.mem_missing_iff
#print axioms Latc.PaperD.General.mem_MissingNonempty_iff
#print axioms Latc.PaperD.General.mem_Complete_iff
#print axioms Latc.PaperD.General.coe_missing_map_toList
#print axioms Latc.PaperD.General.missingNonempty_finset_npComplete
#print axioms Latc.PaperD.General.complete_finset_coNPComplete

-- #P membership and #P-completeness of counting |M(T₀)| (`LatcComplexity/Counting.lean`)
#print axioms Latc.PaperD.rowClause_polyTime
#print axioms Latc.PaperD.toSharpSAT_polyTime
#print axioms Latc.PaperD.mem_vars_toSharpSAT
#print axioms Latc.PaperD.any_zip_iff
#print axioms Latc.PaperD.eval_toSharpSAT
#print axioms Latc.PaperD.countMissing_eq_sharpSAT
#print axioms Latc.PaperD.countMissing_reduces_sharpSAT
#print axioms Latc.PaperD.countMissing_mem_SharpP
#print axioms Latc.PaperD.countMissing_sharpPComplete

-- #P-completeness of counting |M(T₀)| over general finite domains (`LatcComplexity/CountingGeneral.lean`)
#print axioms Latc.PaperD.General.certState_polyTime
#print axioms Latc.PaperD.General.cverifier_polyTime
#print axioms Latc.PaperD.General.certLen_polyTime
#print axioms Latc.PaperD.General.frames_encList_append_replicate
#print axioms Latc.PaperD.General.certState_certWord
#print axioms Latc.PaperD.General.missingCount_eq_acceptCount
#print axioms Latc.PaperD.General.missingCount_mem_SharpP
#print axioms Latc.PaperD.General.valid_iff_eval
#print axioms Latc.PaperD.General.sharpSAT_eq_missingCount
#print axioms Latc.PaperD.General.sharpSAT_reduces_missingCount
#print axioms Latc.PaperD.General.missingCount_sharpPHard
#print axioms Latc.PaperD.General.missingCount_sharpPComplete

-- The monotone two-literal case (`LatcComplexity/Monotone.lean`)
#print axioms Latc.PaperD.General.ParsimoniousReducible.oneCallReducible
#print axioms Latc.PaperD.General.SharpPHard.oneCallSharpPHard
#print axioms Latc.PaperD.General.OneCallReducible.trans_parsimonious
#print axioms Latc.PaperD.General.OneCallSharpPHard.trans_parsimonious
#print axioms Latc.PaperD.General.sharpSAT_oneCallSharpPHard
#print axioms Latc.PaperD.General.countValidMonotone2_eq_card_validSpace
#print axioms Latc.PaperD.General.inDomains_replicate_one
#print axioms Latc.PaperD.General.valid_replicate_one_of_pos2B
#print axioms Latc.PaperD.General.mem_missingNonempty_of_pos2B
#print axioms Latc.PaperD.General.pos2B_polyTime
#print axioms Latc.PaperD.General.monotone2B_polyTime
#print axioms Latc.PaperD.General.fromMonotone2_polyTime
#print axioms Latc.PaperD.General.pos2B_fromSAT
#print axioms Latc.PaperD.General.sharpMonotone2SAT_eq
#print axioms Latc.PaperD.General.sharpMonotone2SAT_reduces
#print axioms Latc.PaperD.General.countValidMonotone2_mem_SharpP
#print axioms Latc.PaperD.General.countValidMonotone2_oneCallSharpPComplete

-- The binary attribute index (`LatcComplexity/Binary.lean`)
#print axioms Latc.PaperD.General.encInst_to_encInstBin_polyTime
#print axioms Latc.PaperD.General.idReduction
#print axioms Latc.PaperD.General.idParsimonious
#print axioms Latc.PaperD.General.condHoldsBin_eq
#print axioms Latc.PaperD.General.condHoldsBin_polyTime
#print axioms Latc.PaperD.General.checkBin_eq
#print axioms Latc.PaperD.General.checkBin_polyTime
#print axioms Latc.PaperD.General.length_domains_le_bin
#print axioms Latc.PaperD.General.MissingNonempty_mem_NP_bin
#print axioms Latc.PaperD.General.MissingNonempty_npComplete_bin
#print axioms Latc.PaperD.General.Complete_coNPComplete_bin
#print axioms Latc.PaperD.General.missingNonempty_finset_npComplete_bin
#print axioms Latc.PaperD.General.complete_finset_coNPComplete_bin
#print axioms Latc.PaperD.General.certState_polyTime_bin
#print axioms Latc.PaperD.General.cverifier_polyTime_bin
#print axioms Latc.PaperD.General.certLen_polyTime_bin
#print axioms Latc.PaperD.General.missingCount_mem_SharpP_bin
#print axioms Latc.PaperD.General.missingCount_sharpPComplete_bin
#print axioms Latc.PaperD.General.pos2Clauses_polyTime_bin
#print axioms Latc.PaperD.General.pos2B_polyTime_bin
#print axioms Latc.PaperD.General.countValidMonotone2_mem_SharpP_bin
#print axioms Latc.PaperD.General.countValidMonotone2_oneCallSharpPComplete_bin

-- The tractable side (`LatcComplexity/Tractable.lean`)
#print axioms Latc.PaperD.General.length_firstOcc
#print axioms Latc.PaperD.General.map_table
#print axioms Latc.PaperD.General.card_table
#print axioms Latc.PaperD.General.card_univ
#print axioms Latc.PaperD.General.missingCount_eq_of_noConstraints
#print axioms Latc.PaperD.General.length_encNat_le_of_mem
#print axioms Latc.PaperD.General.domProd_polyTime
#print axioms Latc.PaperD.General.distinctRows_polyTime
#print axioms Latc.PaperD.General.countNoCon_polyTime
#print axioms Latc.PaperD.General.missingCountNoConstraints_polyTime
#print axioms Latc.PaperD.General.missing_eq_empty_iff_of_noConstraints
#print axioms Latc.PaperD.General.completeNoConB_polyTime
#print axioms Latc.PaperD.General.completeNoConstraints_mem_P
#print axioms Latc.PaperD.General.missingNonemptyNoConstraints_mem_P
#print axioms Latc.PaperD.General.mem_boundedSections
#print axioms Latc.PaperD.General.length_boundedSections_le
#print axioms Latc.PaperD.General.length_candVals_le
#print axioms Latc.PaperD.General.length_candidateStates_le
#print axioms Latc.PaperD.General.boundedSections_zero
#print axioms Latc.PaperD.General.boundedSections_succ
#print axioms Latc.PaperD.General.boundedSections_polyTime
#print axioms Latc.PaperD.General.candPool_polyTime
#print axioms Latc.PaperD.General.candLists_eq
#print axioms Latc.PaperD.General.candidateStates_polyTime
#print axioms Latc.PaperD.General.exists_unwritten
#print axioms Latc.PaperD.General.mem_candidateStates_iff
#print axioms Latc.PaperD.General.exists_missing_candidate_iff
#print axioms Latc.PaperD.General.someCandidateMissing_polyTime
#print axioms Latc.PaperD.General.someCandidateMissing_iff
#print axioms Latc.PaperD.General.missingNonemptyFixedAttrs_mem_P
#print axioms Latc.PaperD.General.completeFixedAttrs_mem_P
#print axioms Latc.PaperD.General.mem_P_of_mem_P_bin
#print axioms Latc.PaperD.General.completeNoConstraints_mem_P_unary
#print axioms Latc.PaperD.General.missingNonemptyNoConstraints_mem_P_unary
#print axioms Latc.PaperD.General.missingCountNoConstraints_polyTime_unary
#print axioms Latc.PaperD.General.completeFixedAttrs_mem_P_unary
#print axioms Latc.PaperD.General.missingNonemptyFixedAttrs_mem_P_unary

-- (b), counting with at most `k` attributes (`LatcComplexity/Tractable.lean`)
#print axioms Latc.PaperD.General.distinctVals_append_singleton
#print axioms Latc.PaperD.General.mem_distinctVals
#print axioms Latc.PaperD.General.nodup_distinctVals
#print axioms Latc.PaperD.General.unwritten_not_mem
#print axioms Latc.PaperD.General.cls_of_mem
#print axioms Latc.PaperD.General.cls_of_not_mem
#print axioms Latc.PaperD.General.cls_cls
#print axioms Latc.PaperD.General.cls_eq_iff_of_mem
#print axioms Latc.PaperD.General.mem_of_cls_mem
#print axioms Latc.PaperD.General.nodup_classVals
#print axioms Latc.PaperD.General.cls_mem_classVals
#print axioms Latc.PaperD.General.classWeight_le
#print axioms Latc.PaperD.General.card_fiber
#print axioms Latc.PaperD.General.sum_range_eq_classes
#print axioms Latc.PaperD.General.mem_domStates
#print axioms Latc.PaperD.General.nodup_domStates
#print axioms Latc.PaperD.General.validB_iff
#print axioms Latc.PaperD.General.missingCount_eq_length_filter
#print axioms Latc.PaperD.General.validB_map_cls
#print axioms Latc.PaperD.General.foldl_mul_eq
#print axioms Latc.PaperD.General.foldl_add_eq
#print axioms Latc.PaperD.General.boundedSections_cons
#print axioms Latc.PaperD.General.boundedSections_of_le
#print axioms Latc.PaperD.General.length_of_mem_boundedSections
#print axioms Latc.PaperD.General.sum_flatMap
#print axioms Latc.PaperD.General.length_filter_domStates
#print axioms Latc.PaperD.General.missingCount_eq_weighted_of_le
#print axioms Latc.PaperD.General.countClasses_eq
#print axioms Latc.PaperD.General.missingCount_eq_countClasses
#print axioms Latc.PaperD.General.length_classStates_le
#print axioms Latc.PaperD.General.writtenVals_polyTime
#print axioms Latc.PaperD.General.distinctVals_polyTime
#print axioms Latc.PaperD.General.unwritten_polyTime
#print axioms Latc.PaperD.General.classVals_polyTime
#print axioms Latc.PaperD.General.classStates_polyTime
#print axioms Latc.PaperD.General.classWeight_polyTime
#print axioms Latc.PaperD.General.validB_polyTime
#print axioms Latc.PaperD.General.length_encNat_le_of_mem_domains
#print axioms Latc.PaperD.General.classStateWeight_polyTime
#print axioms Latc.PaperD.General.prod_classWeight_le
#print axioms Latc.PaperD.General.classStateWeight_le_domProd
#print axioms Latc.PaperD.General.countClasses_polyTime
#print axioms Latc.PaperD.General.missingCountFixedAttrs_polyTime
#print axioms Latc.PaperD.General.missingCountFixedAttrs_polyTime_unary

-- An explicit degree in the number of attributes (`LatcComplexity/ExplicitDegree.lean`)
#print axioms Latc.PaperD.General.mul_pow_le_pow_add
#print axioms Latc.PaperD.General.XPBounded.of_le
#print axioms Latc.PaperD.General.XPBounded.mono_exp
#print axioms Latc.PaperD.General.XPBounded.add
#print axioms Latc.PaperD.General.XPBounded.const
#print axioms Latc.PaperD.General.XPBounded.of_poly
#print axioms Latc.PaperD.General.XPBounded.const_mul
#print axioms Latc.PaperD.General.XPBounded.size_self
#print axioms Latc.PaperD.General.XPBounded.pow
#print axioms Latc.PaperD.General.XPBounded.pow_mul_succ
#print axioms Latc.PaperD.General.timeAndSpace_of_inO_xp
#print axioms Latc.PaperD.General.inO_pow_of_polyTime
#print axioms Latc.PaperD.General.allSections_eq
#print axioms Latc.PaperD.General.foldl_secStep_invariant
#print axioms Latc.PaperD.General.length_encList_reverse
#print axioms Latc.PaperD.General.length_state_le
#print axioms Latc.PaperD.General.secStep_polyTime
#print axioms Latc.PaperD.General.reverse_polyTime
#print axioms Latc.PaperD.General.fold_bound_arith
#print axioms Latc.PaperD.General.allSections_inO
#print axioms Latc.PaperD.General.one_le_instSize
#print axioms Latc.PaperD.General.pipeline_inO
#print axioms Latc.PaperD.General.candLists_polyTime
#print axioms Latc.PaperD.General.anyCheck_polyTime
#print axioms Latc.PaperD.General.anyCheck_allSections
#print axioms Latc.PaperD.General.someCandidateMissing_inO
#print axioms Latc.PaperD.General.classStateWeight_le_domProd_of_length
#print axioms Latc.PaperD.General.countTest_polyTime
#print axioms Latc.PaperD.General.classLists_polyTime
#print axioms Latc.PaperD.General.countTest_allSections
#print axioms Latc.PaperD.General.missingCount_inO
#print axioms Latc.PaperD.General.timeAndSpace_of_xp
#print axioms Latc.PaperD.General.not_inO
#print axioms Latc.PaperD.General.fixedAttrs_of_timeAndSpace
#print axioms Latc.PaperD.General.withBound_timeAndSpace
#print axioms Latc.PaperD.General.decide_nonempty_eq
#print axioms Latc.PaperD.General.decide_empty_eq
#print axioms Latc.PaperD.General.missingNonempty_explicitDegree
#print axioms Latc.PaperD.General.complete_explicitDegree
#print axioms Latc.PaperD.General.missingCount_explicitDegree
#print axioms Latc.PaperD.General.missingNonemptyFixedAttrs_uniform
#print axioms Latc.PaperD.General.completeFixedAttrs_uniform
#print axioms Latc.PaperD.General.missingCountFixedAttrs_uniform
#print axioms Latc.PaperD.General.missingNonemptyWithBound_explicitDegree
#print axioms Latc.PaperD.General.completeWithBound_explicitDegree
#print axioms Latc.PaperD.General.missingCountWithBound_explicitDegree
