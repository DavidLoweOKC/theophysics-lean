import Final_Lean4_From_Excel

/-!
# Theophysics_LawMechanisms

Strong-law mechanism gates for Laws 1, 2, 9, and 10.

Generic collapse proves that zero kills chi.  Strong-law collapse proves why a
defined domain failure forces the zero before the product is evaluated.
-/

namespace Theophysics.LawMechanisms

open Theophysics.Experiment

------------------------------------------------------------------------
-- Shared product-entry helpers

def stateWithG (g : Nat) : FactorState :=
  { G := g, M := 1, E := 1, S := 1, T := 1, K := 1, R := 1, Q := 1, F := 1, C := 1 }

def stateWithM (m : Nat) : FactorState :=
  { G := 1, M := m, E := 1, S := 1, T := 1, K := 1, R := 1, Q := 1, F := 1, C := 1 }

def stateWithF (f : Nat) : FactorState :=
  { G := 1, M := 1, E := 1, S := 1, T := 1, K := 1, R := 1, Q := 1, F := f, C := 1 }

def stateWithC (c : Nat) : FactorState :=
  { G := 1, M := 1, E := 1, S := 1, T := 1, K := 1, R := 1, Q := 1, F := 1, C := c }

------------------------------------------------------------------------
-- Law 1: G gate / external dependency

structure Law1Control where
  receivesExternalInput : Bool
  selfSourcing : Bool
  dependencyDenied : Bool
  boundaryOpen : Bool
deriving DecidableEq, Repr

def GGate (c : Law1Control) : Nat :=
  if c.receivesExternalInput && c.boundaryOpen && !c.selfSourcing && !c.dependencyDenied
  then 1 else 0

def law1Healthy : Law1Control where
  receivesExternalInput := true
  selfSourcing := false
  dependencyDenied := false
  boundaryOpen := true

def law1DependencyDeniedCase : Law1Control where
  receivesExternalInput := true
  selfSourcing := false
  dependencyDenied := true
  boundaryOpen := true

def law1SelfSourcingCase : Law1Control where
  receivesExternalInput := true
  selfSourcing := true
  dependencyDenied := false
  boundaryOpen := true

theorem law1_open_dependent_system_passes_G_gate
    (c : Law1Control)
    (hInput : c.receivesExternalInput = true)
    (hOpen : c.boundaryOpen = true)
    (hSelf : c.selfSourcing = false)
    (hDeny : c.dependencyDenied = false) :
    GGate c = 1 := by
  simp [GGate, hInput, hOpen, hSelf, hDeny]

theorem law1_self_source_forces_G_zero
    (c : Law1Control)
    (h : c.selfSourcing = true) :
    GGate c = 0 := by
  simp [GGate, h]

theorem law1_dependency_denial_forces_G_zero
    (c : Law1Control)
    (h : c.dependencyDenied = true) :
    GGate c = 0 := by
  simp [GGate, h]

theorem law1_closed_boundary_forces_G_zero
    (c : Law1Control)
    (h : c.boundaryOpen = false) :
    GGate c = 0 := by
  simp [GGate, h]

theorem law1_external_input_but_dependency_denied_fails :
    GGate law1DependencyDeniedCase = 0 := by
  rfl

theorem law1_open_boundary_but_self_sourcing_fails :
    GGate law1SelfSourcingCase = 0 := by
  rfl

theorem law1_self_source_collapses_chi
    (c : Law1Control)
    (h : c.selfSourcing = true) :
    chi (stateWithG (GGate c)) = 0 := by
  exact G_zero_collapses_chi (stateWithG (GGate c))
    (by simp [stateWithG, law1_self_source_forces_G_zero c h])

theorem law1_dependency_denial_collapses_chi
    (c : Law1Control)
    (h : c.dependencyDenied = true) :
    chi (stateWithG (GGate c)) = 0 := by
  exact G_zero_collapses_chi (stateWithG (GGate c))
    (by simp [stateWithG, law1_dependency_denial_forces_G_zero c h])

theorem law1_closed_boundary_collapses_chi
    (c : Law1Control)
    (h : c.boundaryOpen = false) :
    chi (stateWithG (GGate c)) = 0 := by
  exact G_zero_collapses_chi (stateWithG (GGate c))
    (by simp [stateWithG, law1_closed_boundary_forces_G_zero c h])

------------------------------------------------------------------------
-- Law 2: M gate / reference standard and alignment

structure Law2Control where
  referenceStandardPresent : Bool
  referenceAcknowledged : Bool
  directionDefined : Bool
  aligned : Bool
deriving DecidableEq, Repr

def MGate (c : Law2Control) : Nat :=
  if c.referenceStandardPresent && c.referenceAcknowledged && c.directionDefined && c.aligned
  then 1 else 0

def law2Healthy : Law2Control where
  referenceStandardPresent := true
  referenceAcknowledged := true
  directionDefined := true
  aligned := true

def law2UnacknowledgedReferenceCase : Law2Control where
  referenceStandardPresent := true
  referenceAcknowledged := false
  directionDefined := true
  aligned := true

def law2MisalignedCase : Law2Control where
  referenceStandardPresent := true
  referenceAcknowledged := true
  directionDefined := true
  aligned := false

theorem law2_aligned_reference_system_passes_M_gate
    (c : Law2Control)
    (hRef : c.referenceStandardPresent = true)
    (hAck : c.referenceAcknowledged = true)
    (hDir : c.directionDefined = true)
    (hAlign : c.aligned = true) :
    MGate c = 1 := by
  simp [MGate, hRef, hAck, hDir, hAlign]

theorem law2_no_reference_forces_M_zero
    (c : Law2Control)
    (h : c.referenceStandardPresent = false) :
    MGate c = 0 := by
  simp [MGate, h]

theorem law2_reference_denial_forces_M_zero
    (c : Law2Control)
    (h : c.referenceAcknowledged = false) :
    MGate c = 0 := by
  simp [MGate, h]

theorem law2_directionless_motion_forces_M_zero
    (c : Law2Control)
    (h : c.directionDefined = false) :
    MGate c = 0 := by
  simp [MGate, h]

theorem law2_misalignment_forces_M_zero
    (c : Law2Control)
    (h : c.aligned = false) :
    MGate c = 0 := by
  simp [MGate, h]

theorem law2_reference_present_but_unacknowledged_fails :
    MGate law2UnacknowledgedReferenceCase = 0 := by
  rfl

theorem law2_direction_defined_but_misaligned_fails :
    MGate law2MisalignedCase = 0 := by
  rfl

theorem law2_no_reference_collapses_chi
    (c : Law2Control)
    (h : c.referenceStandardPresent = false) :
    chi (stateWithM (MGate c)) = 0 := by
  exact M_zero_collapses_chi (stateWithM (MGate c))
    (by simp [stateWithM, law2_no_reference_forces_M_zero c h])

theorem law2_reference_denial_collapses_chi
    (c : Law2Control)
    (h : c.referenceAcknowledged = false) :
    chi (stateWithM (MGate c)) = 0 := by
  exact M_zero_collapses_chi (stateWithM (MGate c))
    (by simp [stateWithM, law2_reference_denial_forces_M_zero c h])

theorem law2_misalignment_collapses_chi
    (c : Law2Control)
    (h : c.aligned = false) :
    chi (stateWithM (MGate c)) = 0 := by
  exact M_zero_collapses_chi (stateWithM (MGate c))
    (by simp [stateWithM, law2_misalignment_forces_M_zero c h])

------------------------------------------------------------------------
-- Law 9: F gate / identity preservation and moral conservation

structure Law9Control where
  identityPreserved : Bool
  transformationTracked : Bool
  conservationLedgerClosed : Bool
  erasesHistory : Bool
deriving DecidableEq, Repr

def FGate (c : Law9Control) : Nat :=
  if c.identityPreserved && c.transformationTracked && c.conservationLedgerClosed && !c.erasesHistory
  then 1 else 0

def law9Healthy : Law9Control where
  identityPreserved := true
  transformationTracked := true
  conservationLedgerClosed := true
  erasesHistory := false

def law9UntrackedCase : Law9Control where
  identityPreserved := true
  transformationTracked := false
  conservationLedgerClosed := true
  erasesHistory := false

def law9OpenLedgerCase : Law9Control where
  identityPreserved := true
  transformationTracked := true
  conservationLedgerClosed := false
  erasesHistory := false

theorem law9_tracked_identity_preservation_passes_F_gate
    (c : Law9Control)
    (hId : c.identityPreserved = true)
    (hTrack : c.transformationTracked = true)
    (hLedger : c.conservationLedgerClosed = true)
    (hErase : c.erasesHistory = false) :
    FGate c = 1 := by
  simp [FGate, hId, hTrack, hLedger, hErase]

theorem law9_identity_erasure_forces_F_zero
    (c : Law9Control)
    (h : c.identityPreserved = false) :
    FGate c = 0 := by
  simp [FGate, h]

theorem law9_untracked_transformation_forces_F_zero
    (c : Law9Control)
    (h : c.transformationTracked = false) :
    FGate c = 0 := by
  simp [FGate, h]

theorem law9_open_ledger_forces_F_zero
    (c : Law9Control)
    (h : c.conservationLedgerClosed = false) :
    FGate c = 0 := by
  simp [FGate, h]

theorem law9_history_erasure_forces_F_zero
    (c : Law9Control)
    (h : c.erasesHistory = true) :
    FGate c = 0 := by
  simp [FGate, h]

theorem law9_identity_preserved_but_untracked_fails :
    FGate law9UntrackedCase = 0 := by
  rfl

theorem law9_transformation_tracked_but_ledger_open_fails :
    FGate law9OpenLedgerCase = 0 := by
  rfl

theorem law9_identity_erasure_collapses_chi
    (c : Law9Control)
    (h : c.identityPreserved = false) :
    chi (stateWithF (FGate c)) = 0 := by
  exact F_zero_collapses_chi (stateWithF (FGate c))
    (by simp [stateWithF, law9_identity_erasure_forces_F_zero c h])

theorem law9_untracked_transformation_collapses_chi
    (c : Law9Control)
    (h : c.transformationTracked = false) :
    chi (stateWithF (FGate c)) = 0 := by
  exact F_zero_collapses_chi (stateWithF (FGate c))
    (by simp [stateWithF, law9_untracked_transformation_forces_F_zero c h])

theorem law9_open_ledger_collapses_chi
    (c : Law9Control)
    (h : c.conservationLedgerClosed = false) :
    chi (stateWithF (FGate c)) = 0 := by
  exact F_zero_collapses_chi (stateWithF (FGate c))
    (by simp [stateWithF, law9_open_ledger_forces_F_zero c h])

------------------------------------------------------------------------
-- Law 10: C gate / whole-system integration

structure Law10Control where
  globallyIntegrated : Bool
  locallySuccessful : Bool
  fragmentsWhole : Bool
  contradictionBound : Bool
deriving DecidableEq, Repr

def CGate (c : Law10Control) : Nat :=
  if c.globallyIntegrated && !c.fragmentsWhole && c.contradictionBound
  then 1 else 0

def law10Healthy : Law10Control where
  globallyIntegrated := true
  locallySuccessful := true
  fragmentsWhole := false
  contradictionBound := true

def law10FragmentedLocalSuccessCase : Law10Control where
  globallyIntegrated := false
  locallySuccessful := true
  fragmentsWhole := true
  contradictionBound := true

def law10UnboundContradictionCase : Law10Control where
  globallyIntegrated := true
  locallySuccessful := true
  fragmentsWhole := false
  contradictionBound := false

theorem law10_integrated_whole_system_passes_C_gate
    (c : Law10Control)
    (hGlobal : c.globallyIntegrated = true)
    (hFrag : c.fragmentsWhole = false)
    (hBound : c.contradictionBound = true) :
    CGate c = 1 := by
  simp [CGate, hGlobal, hFrag, hBound]

theorem law10_fragmentation_forces_C_zero
    (c : Law10Control)
    (h : c.fragmentsWhole = true) :
    CGate c = 0 := by
  simp [CGate, h]

theorem law10_local_success_without_integration_forces_C_zero
    (c : Law10Control)
    (hLocal : c.locallySuccessful = true)
    (hGlobal : c.globallyIntegrated = false) :
    CGate c = 0 := by
  simp [CGate, hGlobal]

theorem law10_unbound_contradiction_forces_C_zero
    (c : Law10Control)
    (h : c.contradictionBound = false) :
    CGate c = 0 := by
  simp [CGate, h]

theorem law10_local_success_but_fragmented_fails :
    CGate law10FragmentedLocalSuccessCase = 0 := by
  rfl

theorem law10_global_claim_with_unbound_contradiction_fails :
    CGate law10UnboundContradictionCase = 0 := by
  rfl

theorem law10_fragmentation_collapses_chi
    (c : Law10Control)
    (h : c.fragmentsWhole = true) :
    chi (stateWithC (CGate c)) = 0 := by
  exact C_zero_collapses_chi (stateWithC (CGate c))
    (by simp [stateWithC, law10_fragmentation_forces_C_zero c h])

theorem law10_local_success_without_integration_collapses_chi
    (c : Law10Control)
    (hLocal : c.locallySuccessful = true)
    (hGlobal : c.globallyIntegrated = false) :
    chi (stateWithC (CGate c)) = 0 := by
  exact C_zero_collapses_chi (stateWithC (CGate c))
    (by simp [stateWithC, law10_local_success_without_integration_forces_C_zero c hLocal hGlobal])

theorem law10_unbound_contradiction_collapses_chi
    (c : Law10Control)
    (h : c.contradictionBound = false) :
    chi (stateWithC (CGate c)) = 0 := by
  exact C_zero_collapses_chi (stateWithC (CGate c))
    (by simp [stateWithC, law10_unbound_contradiction_forces_C_zero c h])

------------------------------------------------------------------------
-- Combined mechanism marker

theorem strong_law_mechanism_marker :
    GGate law1Healthy = 1 ∧
    MGate law2Healthy = 1 ∧
    FGate law9Healthy = 1 ∧
    CGate law10Healthy = 1 ∧
    GGate law1SelfSourcingCase = 0 ∧
    MGate law2UnacknowledgedReferenceCase = 0 ∧
    FGate law9UntrackedCase = 0 ∧
    CGate law10FragmentedLocalSuccessCase = 0 := by
  decide

end Theophysics.LawMechanisms
