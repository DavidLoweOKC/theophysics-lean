import Std

/-!
# Theophysics_DelayedChoice

Finite delayed-choice / quantum-eraser shape layer.

This module does not attempt to derive quantum mechanics from first principles.
It records the structural claim that the delayed-choice quantum eraser uses:
later idler information classifies already-recorded signal events into
different coincidence subsets, while the unsorted local signal pattern remains
unchanged.

The intended bridge to Trinity Actualization is the three-role decomposition:
generation of alternatives, structuring by available/erased which-path
information, and actualization into a recorded event/subset.
-/

namespace Theophysics.DelayedChoice

inductive IdlerDetector where
  | D1
  | D2
  | D3
  | D4
deriving DecidableEq, Repr

inductive WhichPathStatus where
  | erased
  | preserved
deriving DecidableEq, Repr

inductive ConditionalPattern where
  | interference
  | antiInterference
  | noInterference
deriving DecidableEq, Repr

inductive RawSignalPattern where
  | noVisibleInterference
deriving DecidableEq, Repr

inductive TemporalOrder where
  | signalFirst
  | idlerFirst
deriving DecidableEq, Repr

def whichPathStatus : IdlerDetector -> WhichPathStatus
  | IdlerDetector.D1 => WhichPathStatus.erased
  | IdlerDetector.D2 => WhichPathStatus.erased
  | IdlerDetector.D3 => WhichPathStatus.preserved
  | IdlerDetector.D4 => WhichPathStatus.preserved

def conditionalPattern : IdlerDetector -> ConditionalPattern
  | IdlerDetector.D1 => ConditionalPattern.interference
  | IdlerDetector.D2 => ConditionalPattern.antiInterference
  | IdlerDetector.D3 => ConditionalPattern.noInterference
  | IdlerDetector.D4 => ConditionalPattern.noInterference

def isInterferenceLike : ConditionalPattern -> Bool
  | ConditionalPattern.interference => true
  | ConditionalPattern.antiInterference => true
  | ConditionalPattern.noInterference => false

def rawSignalPattern (_order : TemporalOrder) (_detector : IdlerDetector) :
    RawSignalPattern :=
  RawSignalPattern.noVisibleInterference

def delayedClassification (_order : TemporalOrder) (detector : IdlerDetector) :
    ConditionalPattern :=
  conditionalPattern detector

theorem D1_erases_which_path :
    whichPathStatus IdlerDetector.D1 = WhichPathStatus.erased := by
  rfl

theorem D2_erases_which_path :
    whichPathStatus IdlerDetector.D2 = WhichPathStatus.erased := by
  rfl

theorem D3_preserves_which_path :
    whichPathStatus IdlerDetector.D3 = WhichPathStatus.preserved := by
  rfl

theorem D4_preserves_which_path :
    whichPathStatus IdlerDetector.D4 = WhichPathStatus.preserved := by
  rfl

theorem erased_subsets_are_interference_like
    (detector : IdlerDetector)
    (h : whichPathStatus detector = WhichPathStatus.erased) :
    isInterferenceLike (conditionalPattern detector) = true := by
  cases detector <;> simp [whichPathStatus, conditionalPattern, isInterferenceLike] at h |-

theorem preserved_subsets_are_not_interference_like
    (detector : IdlerDetector)
    (h : whichPathStatus detector = WhichPathStatus.preserved) :
    isInterferenceLike (conditionalPattern detector) = false := by
  cases detector <;> simp [whichPathStatus, conditionalPattern, isInterferenceLike] at h |-

theorem raw_signal_pattern_invariant_under_later_idler_classification
    (order : TemporalOrder) (d1 d2 : IdlerDetector) :
    rawSignalPattern order d1 = rawSignalPattern order d2 := by
  rfl

theorem temporal_order_does_not_change_classification
    (o1 o2 : TemporalOrder) (detector : IdlerDetector) :
    delayedClassification o1 detector = delayedClassification o2 detector := by
  rfl

theorem no_retrocausal_signal_in_raw_distribution
    (o1 o2 : TemporalOrder) (d1 d2 : IdlerDetector) :
    rawSignalPattern o1 d1 = rawSignalPattern o2 d2 := by
  rfl

inductive ActualizationRole where
  | generator
  | structurer
  | actualizer
deriving DecidableEq, Repr

inductive ActualizationSystem where
  | singleOperator
  | generatorActualizerOnly
  | generatorStructurerOnly
  | structurerActualizerOnly
  | threeOperator
  | unstructuredChoice
deriving DecidableEq, Repr

def hasGenerator : ActualizationSystem -> Bool
  | ActualizationSystem.singleOperator => true
  | ActualizationSystem.generatorActualizerOnly => true
  | ActualizationSystem.generatorStructurerOnly => true
  | ActualizationSystem.structurerActualizerOnly => false
  | ActualizationSystem.threeOperator => true
  | ActualizationSystem.unstructuredChoice => false

def hasStructurer : ActualizationSystem -> Bool
  | ActualizationSystem.singleOperator => false
  | ActualizationSystem.generatorActualizerOnly => false
  | ActualizationSystem.generatorStructurerOnly => true
  | ActualizationSystem.structurerActualizerOnly => true
  | ActualizationSystem.threeOperator => true
  | ActualizationSystem.unstructuredChoice => false

def hasActualizer : ActualizationSystem -> Bool
  | ActualizationSystem.singleOperator => true
  | ActualizationSystem.generatorActualizerOnly => true
  | ActualizationSystem.generatorStructurerOnly => false
  | ActualizationSystem.structurerActualizerOnly => true
  | ActualizationSystem.threeOperator => true
  | ActualizationSystem.unstructuredChoice => false

def resolvesDelayedChoiceGate (system : ActualizationSystem) : Bool :=
  hasGenerator system && hasStructurer system && hasActualizer system

theorem three_operator_resolves_delayed_choice_gate :
    resolvesDelayedChoiceGate ActualizationSystem.threeOperator = true := by
  rfl

theorem only_three_operator_resolves_delayed_choice_gate
    (system : ActualizationSystem)
    (h : resolvesDelayedChoiceGate system = true) :
    system = ActualizationSystem.threeOperator := by
  cases system <;>
    simp [resolvesDelayedChoiceGate, hasGenerator, hasStructurer, hasActualizer] at h |-

theorem single_operator_delayed_choice_invalid :
    resolvesDelayedChoiceGate ActualizationSystem.singleOperator = false := by
  rfl

theorem generator_actualizer_without_structurer_invalid :
    resolvesDelayedChoiceGate ActualizationSystem.generatorActualizerOnly = false := by
  rfl

theorem generator_structurer_without_actualizer_invalid :
    resolvesDelayedChoiceGate ActualizationSystem.generatorStructurerOnly = false := by
  rfl

theorem structurer_actualizer_without_generator_invalid :
    resolvesDelayedChoiceGate ActualizationSystem.structurerActualizerOnly = false := by
  rfl

theorem unstructured_choice_invalid :
    resolvesDelayedChoiceGate ActualizationSystem.unstructuredChoice = false := by
  rfl

end Theophysics.DelayedChoice
