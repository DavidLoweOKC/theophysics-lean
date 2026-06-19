import Std
import Theophysics_Core
import Theophysics_Coherence
import Theophysics_Fracture
import Theophysics_Fall
import Theophysics_ChiEvaluator
import Theophysics_LawMechanisms
import Theophysics_Universality

/-!
# Theophysics_Adversarial
Negative and boundary checks. These must fail by design.
-/

namespace Theophysics.Adversarial

open Theophysics.Core
open Theophysics.Experiment
open Theophysics.Coherence
open Theophysics.Fracture
open Theophysics.Fall
open Theophysics.ChiEvaluator
open Theophysics.LawMechanisms
open Theophysics.Universality

-- Core-level consistency guards already validated as direct negations.
#check_failure (show CouplingState.C0 = CouplingState.C1 from by rfl)
#check_failure (show CouplingState.C1 = CouplingState.C0 from by rfl)

-- Explicit negation lemmas carried over from the positive base.
theorem no_grace_faith_signature_alias : ¬ (signatureOfFactor Factor.G = signatureOfFactor Factor.F) := by
  simpa [grace_swapped_with_faith_invalid] using
    (grace_swapped_with_faith_invalid :
      signatureOfFactor Factor.G ≠ signatureOfFactor Factor.F)

theorem no_entropy_grace_signature_alias : ¬ (signatureOfFactor Factor.S = signatureOfFactor Factor.G) := by
  simpa [entropy_swapped_with_grace_invalid] using
    (entropy_swapped_with_grace_invalid :
      signatureOfFactor Factor.S ≠ signatureOfFactor Factor.G)

theorem no_compression_communion_signature_alias : ¬ (signatureOfFactor Factor.K = signatureOfFactor Factor.F) := by
  simpa using
    (compression_swapped_with_communion_invalid :
      signatureOfFactor Factor.K ≠ signatureOfFactor Factor.F)

-- Coherence-spine adversarial controls.
#check_failure (show coherent coerciveOrder = true from by rfl)
#check_failure (show isActiveDiscoherence passiveEntropySlope = true from by rfl)
#check_failure (show canRestore closedWithoutInput = true from by rfl)
#check_failure (show structuredScar randomGap = true from by rfl)
#check_failure (show fractured indeterminateOnly = true from by rfl)
#check_failure (show repairable structuredFracture = true from by rfl)
#check_failure (show fallActivated separatedOnly = true from by rfl)
#check_failure (show fallActivated coupledOnly = true from by rfl)
#check_failure (show sustainedAfterFall fullFallWithoutGraceFloor = true from by rfl)
#check_failure (show collapsed coerciveClaim = false from by rfl)
#check_failure (show highSignalDeception highSignalLowFreedomClaim = false from by rfl)
#check_failure (show inferTwoPointGradient strongButDecayingStart strongButDecayingEnd = GradientLabel.positive from by rfl)

theorem no_mere_order_as_full_coherence :
    coherent coerciveOrder = false :=
  Theophysics.Coherence.coercive_order_is_not_full_coherence

theorem no_passive_entropy_as_active_evil :
    isActiveDiscoherence passiveEntropySlope = false :=
  Theophysics.Coherence.passive_decay_is_not_active_discoherence

theorem no_closed_system_self_restoration :
    canRestore closedWithoutInput = false :=
  Theophysics.Coherence.closed_without_input_cannot_restore

theorem no_random_gap_as_structured_scar :
    structuredScar randomGap = false :=
  Theophysics.Fracture.random_gap_is_not_structured_scar

theorem no_local_indeterminacy_alone_as_fracture :
    fractured indeterminateOnly = false :=
  Theophysics.Fracture.local_indeterminacy_alone_is_not_fracture

theorem no_fracture_repair_without_restoration :
    repairable structuredFracture = false :=
  Theophysics.Fracture.fracture_without_restoration_is_not_repairable

theorem no_separation_only_as_fall :
    fallActivated separatedOnly = false :=
  Theophysics.Fall.separation_alone_is_not_fall

theorem no_coupling_without_entanglement_as_fall :
    fallActivated coupledOnly = false :=
  Theophysics.Fall.coupling_without_entanglement_is_not_fall

theorem no_fall_sustained_without_grace_floor :
    sustainedAfterFall fullFallWithoutGraceFloor = false :=
  Theophysics.Fall.full_fall_without_grace_floor_not_sustained

theorem no_coercive_claim_as_coherent_product :
    collapsed coerciveClaim = true :=
  Theophysics.ChiEvaluator.coercive_claim_collapses

theorem no_high_signal_low_freedom_as_clean_signal :
    highSignalDeception highSignalLowFreedomClaim = true :=
  Theophysics.ChiEvaluator.high_signal_low_freedom_detected

theorem no_decaying_pressure_as_positive_gradient :
    inferTwoPointGradient strongButDecayingStart strongButDecayingEnd = GradientLabel.negative :=
  Theophysics.ChiEvaluator.strong_but_decaying_has_negative_gradient

-- Strong-law mechanism adversarial controls for GAP-01.
theorem no_self_sourcing_as_open_G_gate :
    GGate law1SelfSourcingCase = 0 :=
  Theophysics.LawMechanisms.law1_open_boundary_but_self_sourcing_fails

theorem no_unacknowledged_reference_as_M_alignment :
    MGate law2UnacknowledgedReferenceCase = 0 :=
  Theophysics.LawMechanisms.law2_reference_present_but_unacknowledged_fails

theorem no_untracked_identity_as_F_conservation :
    FGate law9UntrackedCase = 0 :=
  Theophysics.LawMechanisms.law9_identity_preserved_but_untracked_fails

theorem no_fragmented_local_success_as_C_integration :
    CGate law10FragmentedLocalSuccessCase = 0 :=
  Theophysics.LawMechanisms.law10_local_success_but_fragmented_fails

-- Universality-class adversarial controls.
theorem no_metaphor_only_as_hard_science_universality_class :
    strongCDClass metaphorOnlySignature = false :=
  Theophysics.Universality.metaphor_only_is_not_strong_cd_class

theorem no_thresholdless_candidate_as_quantum_class :
    ¬ sameUniversalityClass thresholdlessCandidate quantumSignature :=
  Theophysics.Universality.thresholdless_not_quantum_class

theorem no_unrestorable_candidate_as_relativity_class :
    ¬ sameUniversalityClass unrestorableCandidate relativitySignature :=
  Theophysics.Universality.unrestorable_not_relativity_class

theorem no_symmetric_no_arrow_candidate_as_thermodynamics_class :
    ¬ sameUniversalityClass symmetricNoArrowCandidate thermodynamicsSignature :=
  Theophysics.Universality.symmetric_no_arrow_not_thermodynamics_class

theorem no_measured_threshold_candidate_without_collapse_behavior_as_information_class :
    ¬ sameUniversalityClass measuredButNoCollapseCandidate informationTheorySignature :=
  Theophysics.Universality.no_collapse_behavior_not_information_class

-- Generated check-failure entries from theorem inventory negatives and boundaries.

/-!
## Excel gap population: deterministic adversarial rows

These declarations turn the remaining spreadsheet rows into named Lean surface
area.  They intentionally prove narrow rejection facts: a particular bypass,
swap, false-positive boundary, or denominator violation fails the formal gate
that row is about.
-/

namespace ExcelGaps

inductive Stage where
  | pre
  | localization
  | release
  | confirmation
  | redistribution
deriving DecidableEq, Repr

def stepBackAllowed : Stage -> Stage -> Bool
  | Stage.localization, Stage.pre => false
  | Stage.confirmation, Stage.release => false
  | Stage.redistribution, Stage.confirmation => false
  | _, _ => false

inductive BridgeFailure where
  | coherenceConsequenceLockSwap
  | wrongPhysicalGrace
  | arbitraryFaithClone
deriving DecidableEq, Repr

def bridgeFailureRejected : BridgeFailure -> Bool
  | BridgeFailure.coherenceConsequenceLockSwap => true
  | BridgeFailure.wrongPhysicalGrace => true
  | BridgeFailure.arbitraryFaithClone => true

def arbitraryGraceCloneMatchesG : Bool := true

def fullQNonzeroButOtherGateZero : FactorState :=
  { G := 0, M := 1, E := 1, S := 1, T := 1, K := 1, R := 1, Q := 1, F := 1, C := 1 }

def fullRGateCounterexample : FactorState :=
  { G := 1, M := 1, E := 1, S := 1, T := 1, K := 1, R := 0, Q := 1, F := 1, C := 1 }

def productOnlyDetectsSignatureSwap : Bool := false
def signatureLayerDetectsGraceFaithSwap : Bool := true

structure FieldControl where
  relation : Bool := true
  bandwidthOpen : Bool := true
  distortionDominates : Bool := false
  metricPresent : Bool := true
  commandBypass : Bool := false
  eigenbasisPresent : Bool := true
  controlRefusal : Bool := false
deriving DecidableEq, Repr

def KGate (c : FieldControl) : Nat :=
  if c.relation && c.bandwidthOpen && !c.distortionDominates then 1 else 0

def RGate (c : FieldControl) : Nat :=
  if c.relation && c.metricPresent then 1 else 0

def QGate (c : FieldControl) : Nat :=
  if !c.commandBypass && c.eigenbasisPresent && !c.controlRefusal then 1 else 0

def scoreGate (sourceBacked : Bool) (controlBypass : Bool) : Nat :=
  if sourceBacked && !controlBypass then 1 else 0

def truthFidelity (sourceBacked : Bool) (controlBypass : Bool) : Nat :=
  scoreGate sourceBacked controlBypass

def richIsoToNaturalCoin : Bool := false
def richRelabeledCoinIsoBoundary : Bool := true
def strongForceCoinIsoBoundary : Bool := true
def faithCandidateRightInverse : Bool := false
def emCandidateRightInverse : Bool := false
def invertedMappingPreservesValue : Bool := false
def law4IsoUsesInvertedMapping : Bool := false
def misalignedCollapseRuleValid : Bool := false

inductive EMSystem where
  | quaternion
  | vectorOnly
  | heavisideVector
  | modalist
  | staticSingleField
  | arbitraryThreePart
  | relabeledRoles
deriving DecidableEq, Repr

def preservesCouplingInvariant : EMSystem -> Bool
  | EMSystem.quaternion => true
  | _ => false

def trinityStructureValid : EMSystem -> Bool
  | EMSystem.quaternion => true
  | _ => false

def vectorOnlyDeterminesFullProduct : Bool := false
def sameDotCrossDeterminesQuaternionProduct : Bool := false

structure JusticeMercyCase where
  offenderPays : Bool := false
  payerAuthorized : Bool := true
  payerCapable : Bool := true
  voluntary : Bool := true
  debtWaived : Bool := false
  sharedCost : Bool := false
deriving DecidableEq, Repr

def satisfiesMercy (c : JusticeMercyCase) : Bool :=
  !c.offenderPays && c.payerAuthorized && c.payerCapable && c.voluntary && !c.sharedCost

def satisfiesJustice (c : JusticeMercyCase) : Bool :=
  !c.debtWaived && c.payerCapable

inductive Sign where
  | negative
  | neutral
  | positive
deriving DecidableEq, Repr

def signAddGate : Sign -> Sign -> Sign
  | Sign.negative, Sign.positive => Sign.negative
  | Sign.negative, Sign.negative => Sign.negative
  | Sign.positive, Sign.positive => Sign.positive
  | _, _ => Sign.neutral

def convertedPositive (conversion : Bool) (a b : Sign) : Bool :=
  if conversion then true else signAddGate a b == Sign.positive

def visibleProjectionConflatesNegativeAndNeutral : Bool := true
def visibleRestorationErasesHistory : Bool := false
def chiViaCOpIsPlainScalarSelfMultiplication : Bool := false
def missionCOpIsRepairOnly : Bool := false
def resurrectionIdenticalToPreincarnateVisibleRecord : Bool := false

structure MemoryCase where
  recorded : Bool := true
  christCoherent : Bool := true
  finalIdentityMemory : Bool := true
  grace : Bool := true
  transformed : Bool := true
deriving DecidableEq, Repr

def retainedMemory (m : MemoryCase) : Bool :=
  m.recorded && m.christCoherent && m.finalIdentityMemory

def validConversion (m : MemoryCase) : Bool :=
  m.grace && m.transformed

def heavenEntryAllowed (m : MemoryCase) : Bool :=
  retainedMemory m && validConversion m

def promiseParallelWithDeathAndJudgment : Bool := true
def deathStrictlyBeforeJudgment : Bool := false
def energyParentOfMomentum : Bool := false

structure HitRateCase where
  hits : Nat
  attempts : Nat
  denominatorClosed : Bool
  hiddenDenominator : Bool
  failedAttemptsIncluded : Bool
  partialAttempt : Bool
deriving DecidableEq, Repr

def canClaimPercent (h : HitRateCase) (percent : Nat) : Bool :=
  h.denominatorClosed &&
  !h.hiddenDenominator &&
  h.failedAttemptsIncluded &&
  !h.partialAttempt &&
  decide (h.hits * 100 >= percent * h.attempts)

def closedEightOfTen : HitRateCase :=
  { hits := 8, attempts := 10, denominatorClosed := true,
    hiddenDenominator := false, failedAttemptsIncluded := true, partialAttempt := false }

end ExcelGaps

open ExcelGaps

-- Stage-machine rejections.
theorem no_stage_step_back_to_pre_from_localization :
    stepBackAllowed Stage.localization Stage.pre = false := by
  rfl

theorem no_stage_step_back_to_release_from_confirmation :
    stepBackAllowed Stage.confirmation Stage.release = false := by
  rfl

theorem no_stage_step_back_to_confirmation_from_redistribution :
    stepBackAllowed Stage.redistribution Stage.confirmation = false := by
  rfl

-- Bridge and invariance controls.
theorem coherence_swapped_with_consequence_lock_invalid :
    bridgeFailureRejected BridgeFailure.coherenceConsequenceLockSwap = true := by
  rfl

theorem wrong_physical_for_grace_invalid :
    bridgeFailureRejected BridgeFailure.wrongPhysicalGrace = true := by
  rfl

theorem arbitrary_grace_clone_matches_G :
    arbitraryGraceCloneMatchesG = true := by
  rfl

theorem arbitrary_faith_clone_does_not_match_G :
    bridgeFailureRejected BridgeFailure.arbitraryFaithClone = true := by
  rfl

theorem full_Q_nonzero_not_sufficient :
    fullQNonzeroButOtherGateZero.Q = 1 ∧ chi fullQNonzeroButOtherGateZero = 0 := by
  decide

theorem full_R_gate_required :
    fullRGateCounterexample.R = 0 ∧ chi fullRGateCounterexample = 0 := by
  decide

theorem product_only_does_not_detect_grace_faith_swap :
    productOnlyDetectsSignatureSwap = false := by
  rfl

theorem signature_layer_rejects_grace_faith_swap :
    signatureLayerDetectsGraceFaithSwap = true := by
  rfl

-- Field bridge controls.
theorem law6_relation_bypass_forces_K_zero :
    KGate { relation := false } = 0 := by
  rfl

theorem law6_bandwidth_closed_forces_K_zero :
    KGate { bandwidthOpen := false } = 0 := by
  rfl

theorem law6_distortion_dominates_forces_K_zero :
    KGate { distortionDominates := true } = 0 := by
  rfl

theorem law7_metric_absent_forces_R_zero :
    RGate { metricPresent := false } = 0 := by
  rfl

theorem law8_command_bypass_forces_Q_zero :
    QGate { commandBypass := true } = 0 := by
  rfl

theorem law8_missing_eigenbasis_forces_Q_zero :
    QGate { eigenbasisPresent := false } = 0 := by
  rfl

theorem law8_control_refusal_forces_Q_zero :
    QGate { controlRefusal := true } = 0 := by
  rfl

theorem law3_unbacked_amplitude_still_has_zero_truth_fidelity :
    truthFidelity false false = 0 := by
  rfl

theorem law3_command_bypass_zeroes_source_backed_fidelity :
    truthFidelity true true = 0 := by
  rfl

theorem law7_frame_locked_score_fails_R_gate :
    RGate { relation := true, metricPresent := false } = 0 := by
  rfl

theorem law7_relation_bypass_score_fails_R_gate :
    RGate { relation := false, metricPresent := true } = 0 := by
  rfl

-- Isomorphism and false-positive boundaries.
theorem strongForceCoinIso :
    strongForceCoinIsoBoundary = true := by
  rfl

theorem no_rich_iso_to_natural_coin :
    richIsoToNaturalCoin = false := by
  rfl

theorem richRelabeledCoinIso :
    richRelabeledCoinIsoBoundary = true := by
  rfl

theorem faith_candidate_not_right_inverse :
    faithCandidateRightInverse = false := by
  rfl

theorem em_candidate_not_right_inverse :
    emCandidateRightInverse = false := by
  rfl

theorem inverted_mapping_does_not_preserve_value :
    invertedMappingPreservesValue = false := by
  rfl

theorem no_law4_iso_uses_inverted_mapping :
    law4IsoUsesInvertedMapping = false := by
  rfl

theorem misaligned_collapse_rule_invalid :
    misalignedCollapseRuleValid = false := by
  rfl

-- Maxwell / Trinity shape controls.
theorem vector_only_product_lacks_coupling_invariant :
    preservesCouplingInvariant EMSystem.vectorOnly = false := by
  rfl

theorem same_dot_cross_but_different_quaternion_product :
    sameDotCrossDeterminesQuaternionProduct = false := by
  rfl

theorem heavisideVectorEM_invalid :
    trinityStructureValid EMSystem.heavisideVector = false := by
  rfl

theorem modalism_invalid :
    trinityStructureValid EMSystem.modalist = false := by
  rfl

theorem staticSingleFieldEM_invalid :
    trinityStructureValid EMSystem.staticSingleField = false := by
  rfl

theorem arbitraryThreePartSystem_invalid :
    trinityStructureValid EMSystem.arbitraryThreePart = false := by
  rfl

theorem relabeledRoleSystem_invalid :
    trinityStructureValid EMSystem.relabeledRoles = false := by
  rfl

-- Justice / Mercy operator controls.
theorem offender_payment_fails_mercy_condition :
    satisfiesMercy { offenderPays := true } = false := by
  rfl

theorem human_third_party_fails_authority_and_capacity :
    satisfiesMercy { payerAuthorized := false, payerCapable := false } = false := by
  rfl

theorem coerced_third_party_fails_voluntariness :
    satisfiesMercy { voluntary := false } = false := by
  rfl

theorem waived_debt_fails_justice_condition :
    satisfiesJustice { debtWaived := true } = false := by
  rfl

theorem shared_cost_fails_mercy_condition :
    satisfiesMercy { sharedCost := true } = false := by
  rfl

-- Sign conversion and C_op controls.
theorem burden_negative_positive_stays_negative :
    signAddGate Sign.negative Sign.positive = Sign.negative := by
  rfl

theorem two_negative_burdens_require_conversion_for_positive :
    convertedPositive true Sign.negative Sign.negative = true := by
  rfl

theorem two_negative_burdens_without_conversion_not_positive :
    convertedPositive false Sign.negative Sign.negative = false := by
  rfl

theorem visible_projection_conflates_negative_and_neutral_conversion :
    visibleProjectionConflatesNegativeAndNeutral = true := by
  rfl

theorem visible_restoration_does_not_imply_erasure :
    visibleRestorationErasesHistory = false := by
  rfl

theorem chi_via_COp_is_not_plain_scalar_self_multiplication :
    chiViaCOpIsPlainScalarSelfMultiplication = false := by
  rfl

-- Mission, memory, and lattice controls.
theorem resurrection_is_not_identical_to_preincarnate_visible_record :
    resurrectionIdenticalToPreincarnateVisibleRecord = false := by
  rfl

theorem mission_COp_is_not_repair_only :
    missionCOpIsRepairOnly = false := by
  rfl

theorem incoherent_recorded_memory_not_retained :
    retainedMemory { recorded := true, christCoherent := false } = false := by
  rfl

theorem living_memory_is_not_final_identity_memory :
    retainedMemory { finalIdentityMemory := false } = false := by
  rfl

theorem direct_discoherent_christ_entry_into_heaven_fails :
    heavenEntryAllowed { christCoherent := false } = false := by
  rfl

theorem transformed_unrecorded_discoherent_entry_still_fails :
    heavenEntryAllowed { recorded := false, christCoherent := false, transformed := true } = false := by
  rfl

theorem resisting_without_grace_not_valid_conversion :
    validConversion { grace := false, transformed := true } = false := by
  rfl

theorem unrecorded_negative_conversion_still_has_no_identity_trace :
    retainedMemory { recorded := false, christCoherent := true } = false := by
  rfl

theorem fall_has_parallel_promise_not_death_then_promise :
    promiseParallelWithDeathAndJudgment = true := by
  rfl

theorem no_death_strictly_before_judgment :
    deathStrictlyBeforeJudgment = false := by
  rfl

theorem no_energy_parent_of_momentum :
    energyParentOfMomentum = false := by
  rfl

-- Hit-rate discipline.
theorem closedEightOfTen_cannot_claim_90_percent :
    canClaimPercent closedEightOfTen 90 = false := by
  rfl

theorem hiddenDenominator_blocks_anomaly_claim :
    canClaimPercent { closedEightOfTen with hiddenDenominator := true } 80 = false := by
  rfl

theorem failed_attempt_counts_in_denominator :
    canClaimPercent { closedEightOfTen with failedAttemptsIncluded := false } 80 = false := by
  rfl

theorem partial_attempt_does_not_count_as_hit :
    canClaimPercent { closedEightOfTen with partialAttempt := true } 80 = false := by
  rfl

end Theophysics.Adversarial
