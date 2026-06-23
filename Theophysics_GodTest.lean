import Std

/-!
# Theophysics_GodTest

Finite "God-marker" gate model for the Elimination pre-test.

This module does not prove the historical resurrection or Christianity from
neutral premises. It proves a narrower structural claim:

Given the declared jurisdictional gates, only the full Christ-shaped candidate
passes all gates. Counterfeit candidates fail by missing at least one required
property.
-/

namespace Theophysics.GodTest

inductive Gate where
  | sourcehood
  | voluntaryDeathEntry
  | noMoralDebt
  | perfectJustice
  | perfectMercy
  | truthPreservation
  | identityPreservation
  | rightfulDeathVictory
  | nonBorrowedAuthority
  | communicableRestoration
deriving DecidableEq, Repr

inductive Candidate where
  | christMarker
  | rawPower
  | deathAvoider
  | deathSurvivor
  | tricksterEscape
  | technologyRevival
  | mercyWithoutJustice
  | justiceWithoutMercy
  | borrowedVictory
  | identityReplacement
  | privateInnocence
  | impersonalLaw
  | symbolicResurrection
  | selfSalvation
  | cosmicCycle
deriving DecidableEq, Repr

def hasGate : Candidate -> Gate -> Bool
  | Candidate.christMarker, _ => true

  | Candidate.rawPower, Gate.sourcehood => false
  | Candidate.rawPower, Gate.voluntaryDeathEntry => false
  | Candidate.rawPower, Gate.noMoralDebt => false
  | Candidate.rawPower, Gate.perfectJustice => false
  | Candidate.rawPower, Gate.perfectMercy => false
  | Candidate.rawPower, Gate.truthPreservation => false
  | Candidate.rawPower, Gate.identityPreservation => true
  | Candidate.rawPower, Gate.rightfulDeathVictory => false
  | Candidate.rawPower, Gate.nonBorrowedAuthority => false
  | Candidate.rawPower, Gate.communicableRestoration => false

  | Candidate.deathAvoider, Gate.sourcehood => false
  | Candidate.deathAvoider, Gate.voluntaryDeathEntry => false
  | Candidate.deathAvoider, Gate.noMoralDebt => true
  | Candidate.deathAvoider, Gate.perfectJustice => true
  | Candidate.deathAvoider, Gate.perfectMercy => false
  | Candidate.deathAvoider, Gate.truthPreservation => true
  | Candidate.deathAvoider, Gate.identityPreservation => true
  | Candidate.deathAvoider, Gate.rightfulDeathVictory => false
  | Candidate.deathAvoider, Gate.nonBorrowedAuthority => false
  | Candidate.deathAvoider, Gate.communicableRestoration => false

  | Candidate.deathSurvivor, Gate.sourcehood => false
  | Candidate.deathSurvivor, Gate.voluntaryDeathEntry => true
  | Candidate.deathSurvivor, Gate.noMoralDebt => false
  | Candidate.deathSurvivor, Gate.perfectJustice => false
  | Candidate.deathSurvivor, Gate.perfectMercy => false
  | Candidate.deathSurvivor, Gate.truthPreservation => true
  | Candidate.deathSurvivor, Gate.identityPreservation => true
  | Candidate.deathSurvivor, Gate.rightfulDeathVictory => false
  | Candidate.deathSurvivor, Gate.nonBorrowedAuthority => false
  | Candidate.deathSurvivor, Gate.communicableRestoration => false

  | Candidate.tricksterEscape, Gate.sourcehood => false
  | Candidate.tricksterEscape, Gate.voluntaryDeathEntry => true
  | Candidate.tricksterEscape, Gate.noMoralDebt => false
  | Candidate.tricksterEscape, Gate.perfectJustice => false
  | Candidate.tricksterEscape, Gate.perfectMercy => false
  | Candidate.tricksterEscape, Gate.truthPreservation => false
  | Candidate.tricksterEscape, Gate.identityPreservation => true
  | Candidate.tricksterEscape, Gate.rightfulDeathVictory => false
  | Candidate.tricksterEscape, Gate.nonBorrowedAuthority => false
  | Candidate.tricksterEscape, Gate.communicableRestoration => false

  | Candidate.technologyRevival, Gate.sourcehood => false
  | Candidate.technologyRevival, Gate.voluntaryDeathEntry => false
  | Candidate.technologyRevival, Gate.noMoralDebt => false
  | Candidate.technologyRevival, Gate.perfectJustice => false
  | Candidate.technologyRevival, Gate.perfectMercy => false
  | Candidate.technologyRevival, Gate.truthPreservation => true
  | Candidate.technologyRevival, Gate.identityPreservation => false
  | Candidate.technologyRevival, Gate.rightfulDeathVictory => false
  | Candidate.technologyRevival, Gate.nonBorrowedAuthority => false
  | Candidate.technologyRevival, Gate.communicableRestoration => false

  | Candidate.mercyWithoutJustice, Gate.sourcehood => false
  | Candidate.mercyWithoutJustice, Gate.voluntaryDeathEntry => false
  | Candidate.mercyWithoutJustice, Gate.noMoralDebt => false
  | Candidate.mercyWithoutJustice, Gate.perfectJustice => false
  | Candidate.mercyWithoutJustice, Gate.perfectMercy => true
  | Candidate.mercyWithoutJustice, Gate.truthPreservation => false
  | Candidate.mercyWithoutJustice, Gate.identityPreservation => true
  | Candidate.mercyWithoutJustice, Gate.rightfulDeathVictory => false
  | Candidate.mercyWithoutJustice, Gate.nonBorrowedAuthority => false
  | Candidate.mercyWithoutJustice, Gate.communicableRestoration => true

  | Candidate.justiceWithoutMercy, Gate.sourcehood => false
  | Candidate.justiceWithoutMercy, Gate.voluntaryDeathEntry => false
  | Candidate.justiceWithoutMercy, Gate.noMoralDebt => true
  | Candidate.justiceWithoutMercy, Gate.perfectJustice => true
  | Candidate.justiceWithoutMercy, Gate.perfectMercy => false
  | Candidate.justiceWithoutMercy, Gate.truthPreservation => true
  | Candidate.justiceWithoutMercy, Gate.identityPreservation => true
  | Candidate.justiceWithoutMercy, Gate.rightfulDeathVictory => false
  | Candidate.justiceWithoutMercy, Gate.nonBorrowedAuthority => false
  | Candidate.justiceWithoutMercy, Gate.communicableRestoration => false

  | Candidate.borrowedVictory, Gate.sourcehood => false
  | Candidate.borrowedVictory, Gate.voluntaryDeathEntry => true
  | Candidate.borrowedVictory, Gate.noMoralDebt => true
  | Candidate.borrowedVictory, Gate.perfectJustice => true
  | Candidate.borrowedVictory, Gate.perfectMercy => true
  | Candidate.borrowedVictory, Gate.truthPreservation => true
  | Candidate.borrowedVictory, Gate.identityPreservation => true
  | Candidate.borrowedVictory, Gate.rightfulDeathVictory => false
  | Candidate.borrowedVictory, Gate.nonBorrowedAuthority => false
  | Candidate.borrowedVictory, Gate.communicableRestoration => true

  | Candidate.identityReplacement, Gate.sourcehood => false
  | Candidate.identityReplacement, Gate.voluntaryDeathEntry => true
  | Candidate.identityReplacement, Gate.noMoralDebt => false
  | Candidate.identityReplacement, Gate.perfectJustice => false
  | Candidate.identityReplacement, Gate.perfectMercy => false
  | Candidate.identityReplacement, Gate.truthPreservation => false
  | Candidate.identityReplacement, Gate.identityPreservation => false
  | Candidate.identityReplacement, Gate.rightfulDeathVictory => false
  | Candidate.identityReplacement, Gate.nonBorrowedAuthority => false
  | Candidate.identityReplacement, Gate.communicableRestoration => false

  | Candidate.privateInnocence, Gate.sourcehood => false
  | Candidate.privateInnocence, Gate.voluntaryDeathEntry => true
  | Candidate.privateInnocence, Gate.noMoralDebt => true
  | Candidate.privateInnocence, Gate.perfectJustice => true
  | Candidate.privateInnocence, Gate.perfectMercy => false
  | Candidate.privateInnocence, Gate.truthPreservation => true
  | Candidate.privateInnocence, Gate.identityPreservation => true
  | Candidate.privateInnocence, Gate.rightfulDeathVictory => true
  | Candidate.privateInnocence, Gate.nonBorrowedAuthority => false
  | Candidate.privateInnocence, Gate.communicableRestoration => false

  | Candidate.impersonalLaw, Gate.sourcehood => false
  | Candidate.impersonalLaw, Gate.voluntaryDeathEntry => false
  | Candidate.impersonalLaw, Gate.noMoralDebt => true
  | Candidate.impersonalLaw, Gate.perfectJustice => true
  | Candidate.impersonalLaw, Gate.perfectMercy => false
  | Candidate.impersonalLaw, Gate.truthPreservation => true
  | Candidate.impersonalLaw, Gate.identityPreservation => false
  | Candidate.impersonalLaw, Gate.rightfulDeathVictory => false
  | Candidate.impersonalLaw, Gate.nonBorrowedAuthority => false
  | Candidate.impersonalLaw, Gate.communicableRestoration => false

  | Candidate.symbolicResurrection, Gate.sourcehood => false
  | Candidate.symbolicResurrection, Gate.voluntaryDeathEntry => false
  | Candidate.symbolicResurrection, Gate.noMoralDebt => false
  | Candidate.symbolicResurrection, Gate.perfectJustice => false
  | Candidate.symbolicResurrection, Gate.perfectMercy => false
  | Candidate.symbolicResurrection, Gate.truthPreservation => true
  | Candidate.symbolicResurrection, Gate.identityPreservation => false
  | Candidate.symbolicResurrection, Gate.rightfulDeathVictory => false
  | Candidate.symbolicResurrection, Gate.nonBorrowedAuthority => false
  | Candidate.symbolicResurrection, Gate.communicableRestoration => false

  | Candidate.selfSalvation, Gate.sourcehood => false
  | Candidate.selfSalvation, Gate.voluntaryDeathEntry => false
  | Candidate.selfSalvation, Gate.noMoralDebt => false
  | Candidate.selfSalvation, Gate.perfectJustice => false
  | Candidate.selfSalvation, Gate.perfectMercy => false
  | Candidate.selfSalvation, Gate.truthPreservation => false
  | Candidate.selfSalvation, Gate.identityPreservation => true
  | Candidate.selfSalvation, Gate.rightfulDeathVictory => false
  | Candidate.selfSalvation, Gate.nonBorrowedAuthority => false
  | Candidate.selfSalvation, Gate.communicableRestoration => false

  | Candidate.cosmicCycle, Gate.sourcehood => false
  | Candidate.cosmicCycle, Gate.voluntaryDeathEntry => false
  | Candidate.cosmicCycle, Gate.noMoralDebt => false
  | Candidate.cosmicCycle, Gate.perfectJustice => false
  | Candidate.cosmicCycle, Gate.perfectMercy => false
  | Candidate.cosmicCycle, Gate.truthPreservation => false
  | Candidate.cosmicCycle, Gate.identityPreservation => false
  | Candidate.cosmicCycle, Gate.rightfulDeathVictory => false
  | Candidate.cosmicCycle, Gate.nonBorrowedAuthority => false
  | Candidate.cosmicCycle, Gate.communicableRestoration => false

def passesGodMarker (c : Candidate) : Bool :=
  hasGate c Gate.sourcehood &&
  hasGate c Gate.voluntaryDeathEntry &&
  hasGate c Gate.noMoralDebt &&
  hasGate c Gate.perfectJustice &&
  hasGate c Gate.perfectMercy &&
  hasGate c Gate.truthPreservation &&
  hasGate c Gate.identityPreservation &&
  hasGate c Gate.rightfulDeathVictory &&
  hasGate c Gate.nonBorrowedAuthority &&
  hasGate c Gate.communicableRestoration

theorem christ_marker_passes :
    passesGodMarker Candidate.christMarker = true := by
  rfl

theorem raw_power_fails :
    passesGodMarker Candidate.rawPower = false := by
  rfl

theorem death_avoider_fails :
    passesGodMarker Candidate.deathAvoider = false := by
  rfl

theorem death_survivor_fails :
    passesGodMarker Candidate.deathSurvivor = false := by
  rfl

theorem trickster_escape_fails :
    passesGodMarker Candidate.tricksterEscape = false := by
  rfl

theorem technology_revival_fails :
    passesGodMarker Candidate.technologyRevival = false := by
  rfl

theorem mercy_without_justice_fails :
    passesGodMarker Candidate.mercyWithoutJustice = false := by
  rfl

theorem justice_without_mercy_fails :
    passesGodMarker Candidate.justiceWithoutMercy = false := by
  rfl

theorem borrowed_victory_fails :
    passesGodMarker Candidate.borrowedVictory = false := by
  rfl

theorem identity_replacement_fails :
    passesGodMarker Candidate.identityReplacement = false := by
  rfl

theorem private_innocence_fails :
    passesGodMarker Candidate.privateInnocence = false := by
  rfl

theorem impersonal_law_fails :
    passesGodMarker Candidate.impersonalLaw = false := by
  rfl

theorem symbolic_resurrection_fails :
    passesGodMarker Candidate.symbolicResurrection = false := by
  rfl

theorem self_salvation_fails :
    passesGodMarker Candidate.selfSalvation = false := by
  rfl

theorem cosmic_cycle_fails :
    passesGodMarker Candidate.cosmicCycle = false := by
  rfl

theorem only_christ_marker_passes
    (c : Candidate)
    (h : passesGodMarker c = true) :
    c = Candidate.christMarker := by
  cases c <;> simp [passesGodMarker, hasGate] at h |-

end Theophysics.GodTest
