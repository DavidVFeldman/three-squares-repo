/-
Compiled axiom audit. Building this file forces every named theorem to be
elaborated and prints its axiom dependencies into the build transcript;
CI asserts that no axiom beyond propext, Classical.choice, Quot.sound
appears. Names cover all commissioned theorems of Rounds 1-4.
-/
import Round1
import Round2
import Round3
import Round4

#print axioms ThreeSquares.theta_mul
#print axioms ThreeSquares.theta_theta
#print axioms ThreeSquares.theta_hL
#print axioms ThreeSquares.theta_hW
#print axioms ThreeSquares.isSym_strip
#print axioms ThreeSquares.imI_conj
#print axioms ThreeSquares.imI_hW_eq_zero
#print axioms ThreeSquares.alphaCount_even
#print axioms ThreeSquares.normSq_hL_alpha
#print axioms ThreeSquares.normSq_hL_beta
#print axioms ThreeSquares.normSq_hW
#print axioms ThreeSquares.three_squares
#print axioms ThreeSquares.i_mul_hW
#print axioms ThreeSquares.hW_ib_components
#print axioms ThreeSquares.hW_neg_yz
#print axioms ThreeSquares.Rc_zero
#print axioms ThreeSquares.Rc_one
#print axioms ThreeSquares.Rc_two
#print axioms ThreeSquares.census_1_3
#print axioms ThreeSquares.census_2_1
#print axioms ThreeSquares.no_orthogonal_skew
#print axioms ThreeSquares.no_bilinear_233
#print axioms ThreeSquares.mem_allWords
#print axioms ThreeSquares.nodup_allWords
#print axioms ThreeSquares.ia_ia
#print axioms ThreeSquares.ib_ib
#print axioms ThreeSquares.inv_inv
#print axioms ThreeSquares.ia_inv
#print axioms ThreeSquares.ib_inv
#print axioms ThreeSquares.reduced_mirror
#print axioms ThreeSquares.alphaCount_mirror
#print axioms ThreeSquares.betaCount_mirror
#print axioms ThreeSquares.alphaCount_ibMap
#print axioms ThreeSquares.betaCount_ibMap
#print axioms ThreeSquares.reduced_ibMap
#print axioms ThreeSquares.isSym_encode
#print axioms ThreeSquares.reduced_encode
#print axioms ThreeSquares.counts_encode
#print axioms ThreeSquares.bisection_exists
#print axioms ThreeSquares.encode_inj
#print axioms ThreeSquares.nCount_partition
#print axioms ThreeSquares.eCount_symm_alpha
#print axioms ThreeSquares.eCount_symm_beta
#print axioms ThreeSquares.eCount_peel_a
#print axioms ThreeSquares.eCount_peel_b
#print axioms ThreeSquares.pCount_eq
#print axioms ThreeSquares.pCount_eq_Rc
#print axioms ThreeSquares.pbCount_eq_pCount
#print axioms ThreeSquares.censusCount_eq
#print axioms ThreeSquares.census_2_3
#print axioms ThreeSquares.census_1_5
#print axioms ThreeSquares.inv_start
#print axioms ThreeSquares.inv_step
#print axioms ThreeSquares.core
#print axioms ThreeSquares.vecMul_genM
#print axioms ThreeSquares.vecMul_evalM
#print axioms ThreeSquares.swierczkowski_free
#print axioms ThreeSquares.hW_cons
#print axioms ThreeSquares.evalM_cons
#print axioms ThreeSquares.evalM_append
#print axioms ThreeSquares.re_conj_pure
#print axioms ThreeSquares.conjMat_mul
#print axioms ThreeSquares.conjMat_neg
#print axioms ThreeSquares.conjMat_qL
#print axioms ThreeSquares.conjMat_qW
#print axioms ThreeSquares.genM_transpose
#print axioms ThreeSquares.genM_orth
#print axioms ThreeSquares.evalM_orth
#print axioms ThreeSquares.evalM_invRev
#print axioms ThreeSquares.reduced_invRev
#print axioms ThreeSquares.length_eq_of_evalM_eq
#print axioms ThreeSquares.reduced_invRev_append
#print axioms ThreeSquares.genM_cancel
#print axioms ThreeSquares.evalM_inj
#print axioms ThreeSquares.qW_inj_pm
#print axioms ThreeSquares.qmap_hW
#print axioms ThreeSquares.hWgen_inj_pm
#print axioms ThreeSquares.quat_eq_iff_triple
#print axioms ThreeSquares.sign_classification
#print axioms ThreeSquares.ibMap_ne_self
#print axioms ThreeSquares.genR_decomp
#print axioms ThreeSquares.three_dvd_iff
#print axioms ThreeSquares.three_prime_mul
#print axioms ThreeSquares.mesh_unit
#print axioms ThreeSquares.mesh_inv
#print axioms ThreeSquares.colR_unit
#print axioms ThreeSquares.rowR_unit
#print axioms ThreeSquares.evalR_decomp
#print axioms ThreeSquares.rank3_free
#print axioms ThreeSquares.genR_emb
#print axioms ThreeSquares.swierczkowski_free'
#print axioms ThreeSquares.mem_SFin
#print axioms ThreeSquares.SFin_card
#print axioms ThreeSquares.isSym_ibMap
#print axioms ThreeSquares.ibMap_mem_SFin
#print axioms ThreeSquares.orbit_card
#print axioms ThreeSquares.orbit_eq_of_mem
#print axioms ThreeSquares.card_SFin_eq_two_mul
#print axioms ThreeSquares.numClasses_eq
#print axioms ThreeSquares.orbit_eq_iff_sign
