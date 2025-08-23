(**
 * AutomatonTransition - Transition Function for φ-Language Automaton
 * 
 * This module defines the transition function for the finite automaton
 * that recognizes valid φ-strings (no consecutive 11).
 * 
 * SINGLE THEOREM POLICY: This file contains only transition function.
 * ZERO ADMITTED POLICY: All theorems proven with complete proofs ending in Qed.
 * PURE BINARY POLICY: Uses state-based transitions, no string dependencies.
 * 
 * Mathematical Correspondence:
 * - δ: Q × Σ → Q (deterministic transition function)
 * - Implements no-11 constraint via state tracking
 * - Foundation for computational φ-string recognition
 * 
 * Dependencies: PhiBitType.v, AutomatonStateDefinition.v
 *)

(** Standard Coq imports *)
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Arith.Arith.

(** Import our foundations *)
From Foundations Require Import PhiBitType.
From Foundations Require Import AutomatonStateDefinition.

Module AutomatonTransition.

Import PhiBitType.
Import AutomatonStateDefinition.

(** * Transition Function *)

(**
 * Deterministic transition function δ: State × Bit → State
 * Implements the logic to track last bit and detect "11" pattern
 *)
Definition delta (current_state : AutomatonState) (input_bit : PhiBit) : AutomatonState :=
  match current_state, input_bit with
  | q_start, zero => q_zero        (* Start + 0 → last bit is 0 *)
  | q_start, one => q_one          (* Start + 1 → last bit is 1 *)
  | q_zero, zero => q_zero         (* 0 + 0 → still last bit is 0 *)
  | q_zero, one => q_one           (* 0 + 1 → last bit is 1 *)
  | q_one, zero => q_zero          (* 1 + 0 → last bit is 0 *)
  | q_one, one => q_reject         (* 1 + 1 → found "11", reject *)
  | q_reject, _ => q_reject        (* Once rejected, stay rejected *)
  end.

(** * Transition Properties *)

(**
 * Transition function is total (defined for all inputs)
 *)
Theorem delta_total :
  forall (s : AutomatonState) (b : PhiBit), 
    exists s' : AutomatonState, delta s b = s'.
Proof.
  intros s b.
  destruct s, b; eexists; reflexivity.
Qed.

(**
 * Rejection is absorbing (once rejected, always rejected)
 *)
Theorem rejection_absorbing :
  forall b : PhiBit,
    delta q_reject b = q_reject.
Proof.
  intro b.
  destruct b; reflexivity.
Qed.

(**
 * Non-reject states remain non-reject on valid transitions
 *)
Theorem valid_transitions_preserve_acceptance :
  forall (s : AutomatonState) (b : PhiBit),
    s <> q_reject ->
    (s = q_one /\ b = one -> False) ->
    delta s b <> q_reject.
Proof.
  intros s b Hs Hno11.
  destruct s, b; simpl.
  - discriminate.  (* q_start, zero → q_zero ≠ q_reject *)
  - discriminate.  (* q_start, one → q_one ≠ q_reject *)
  - discriminate.  (* q_zero, zero → q_zero ≠ q_reject *)
  - discriminate.  (* q_zero, one → q_one ≠ q_reject *)
  - discriminate.  (* q_one, zero → q_zero ≠ q_reject *)
  - (* q_one, one → q_reject: this case should be impossible by Hno11 *)
    exfalso.
    apply Hno11.
    split; reflexivity.
  - (* q_reject, zero → q_reject: contradicts Hs *)
    exfalso. exact (Hs eq_refl).
  - (* q_reject, one → q_reject: contradicts Hs *)
    exfalso. exact (Hs eq_refl).
Qed.

(**
 * The "11" pattern leads to rejection
 *)
Theorem eleven_pattern_rejects :
  delta q_one one = q_reject.
Proof.
  reflexivity.
Qed.

(**
 * Starting with any single bit keeps us in accepting states
 *)
Theorem single_bit_accepted :
  forall b : PhiBit,
    is_accepting_state (delta initial_state b) = true.
Proof.
  intro b.
  unfold initial_state.
  destruct b; reflexivity.
Qed.

(** * Transition Table *)

(**
 * Complete transition table verification
 *)
Example transition_table :
  delta q_start zero = q_zero /\
  delta q_start one = q_one /\
  delta q_zero zero = q_zero /\
  delta q_zero one = q_one /\
  delta q_one zero = q_zero /\
  delta q_one one = q_reject /\
  delta q_reject zero = q_reject /\
  delta q_reject one = q_reject.
Proof.
  repeat split; reflexivity.
Qed.

(** * Determinism *)

(**
 * The transition function is deterministic
 *)
Theorem delta_deterministic :
  forall (s : AutomatonState) (b : PhiBit) (s1 s2 : AutomatonState),
    delta s b = s1 ->
    delta s b = s2 ->
    s1 = s2.
Proof.
  intros s b s1 s2 H1 H2.
  rewrite H1 in H2.
  exact H2.
Qed.

(** * State Reachability *)

(**
 * All non-reject states are reachable from start
 *)
Theorem non_reject_states_reachable :
  (exists b, delta initial_state b = q_zero) /\
  (exists b, delta initial_state b = q_one) /\
  (initial_state = q_start).
Proof.
  split; [exists zero; reflexivity | split; [exists one; reflexivity | reflexivity]].
Qed.

(** * Module Interface *)

(**
 * Export core transition interface
 *)
Module AutomatonTransitionInterface.
  Definition exported_delta := delta.
  Definition exported_delta_total := delta_total.
  Definition exported_rejection_absorbing := rejection_absorbing.
  Definition exported_valid_transitions_preserve_acceptance := valid_transitions_preserve_acceptance.
  Definition exported_eleven_pattern_rejects := eleven_pattern_rejects.
  Definition exported_single_bit_accepted := single_bit_accepted.
  Definition exported_transition_table := transition_table.
  Definition exported_delta_deterministic := delta_deterministic.
  Definition exported_non_reject_states_reachable := non_reject_states_reachable.
End AutomatonTransitionInterface.

End AutomatonTransition.

(**
 * Module Summary:
 * 
 * This AutomatonTransition module provides the atomic transition function
 * for the φ-language recognition automaton.
 * 
 * Key Achievements:
 * ✓ Single focus: Transition function only
 * ✓ Complete deterministic transitions: All cases covered
 * ✓ No-11 enforcement: Correctly rejects "11" pattern
 * ✓ Absorbing rejection: Once rejected, always rejected
 * ✓ Reachability: All valid states reachable
 * 
 * This atomic module provides the foundation for:
 * - Automaton execution algorithms
 * - φ-language recognition proofs
 * - String acceptance verification
 * - All higher-level automaton operations
 *)

(** End of AutomatonTransition module *)