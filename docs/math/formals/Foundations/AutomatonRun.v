(**
 * AutomatonRun - Execution Function for φ-Language Automaton
 * 
 * This module defines the execution function that runs the automaton
 * on a given φ-string to determine acceptance.
 * 
 * SINGLE THEOREM POLICY: This file contains only the run function.
 * ZERO ADMITTED POLICY: All theorems proven with complete proofs ending in Qed.
 * PURE BINARY POLICY: Uses state-based execution, no string dependencies.
 * 
 * Mathematical Correspondence:
 * - δ*: Q × Σ* → Q (extended transition function)
 * - Implements string acceptance via final state check
 * - Foundation for computational φ-language membership
 * 
 * Dependencies: PhiBitType.v, PhiStringType.v, AutomatonStateDefinition.v, AutomatonTransition.v
 *)

(** Standard Coq imports *)
From Stdlib Require Import Lists.List.
From Stdlib Require Import Bool.Bool.

(** Import our foundations *)
From Foundations Require Import PhiBitType.
From Foundations Require Import PhiStringType.
From Foundations Require Import AutomatonStateDefinition.
From Foundations Require Import AutomatonTransition.

Module AutomatonRun.

Import ListNotations.
Import PhiBitType.
Import PhiStringType.
Import AutomatonStateDefinition.
Import AutomatonTransition.

(** * Extended Transition Function *)

(**
 * Run the automaton on a string, returning the final state
 * δ*: State × String → State
 *)
Fixpoint run_automaton (start_state : AutomatonState) (input : PhiString) : AutomatonState :=
  match input with
  | [] => start_state
  | bit :: rest => run_automaton (delta start_state bit) rest
  end.

(**
 * Run from initial state (most common case)
 *)
Definition accept_string (input : PhiString) : bool :=
  is_accepting_state (run_automaton initial_state input).

(** * Basic Properties *)

(**
 * Empty string execution preserves state
 *)
Theorem run_empty_preserves_state :
  forall s : AutomatonState,
    run_automaton s [] = s.
Proof.
  intro s.
  reflexivity.
Qed.

(**
 * Single bit execution equals single transition
 *)
Theorem run_single_bit :
  forall (s : AutomatonState) (b : PhiBit),
    run_automaton s [b] = delta s b.
Proof.
  intros s b.
  simpl.
  (* After simpl: run_automaton (delta s b) [] = delta s b *)
  reflexivity.
Qed.

(**
 * Running from initial state
 *)
Theorem run_from_initial :
  forall input : PhiString,
    run_automaton initial_state input = run_automaton q_start input.
Proof.
  intro input.
  unfold initial_state.
  reflexivity.
Qed.

(** * Compositional Properties *)

(**
 * Concatenation law: running on concatenated strings
 *)
Theorem run_concatenation :
  forall (s : AutomatonState) (input1 input2 : PhiString),
    run_automaton s (input1 ++ input2) = 
    run_automaton (run_automaton s input1) input2.
Proof.
  intros s input1 input2.
  revert s.
  induction input1 as [|b input1' IH]; intro s.
  - (* input1 = [] *)
    simpl. reflexivity.
  - (* input1 = b :: input1' *)
    simpl.
    apply IH.
Qed.

(**
 * Rejection propagation: once rejected, always rejected
 *)
Theorem rejection_propagates :
  forall input : PhiString,
    run_automaton q_reject input = q_reject.
Proof.
  intro input.
  induction input as [|b input' IH].
  - reflexivity.
  - simpl.
    (* We have: run_automaton (delta q_reject b) input' = q_reject *)
    (* delta q_reject b = q_reject by definition *)
    destruct b; simpl; exact IH.
Qed.

(** * Acceptance Properties *)

(**
 * Empty string is accepted
 *)
Theorem accept_empty_string :
  accept_string [] = true.
Proof.
  unfold accept_string.
  simpl.
  unfold initial_state.
  reflexivity.
Qed.

(**
 * Single bits are accepted
 *)
Theorem accept_single_bits :
  forall b : PhiBit,
    accept_string [b] = true.
Proof.
  intro b.
  unfold accept_string.
  rewrite run_from_initial.
  rewrite run_single_bit.
  apply single_bit_accepted.
Qed.

(**
 * "11" pattern is rejected
 *)
Theorem reject_eleven_pattern :
  accept_string [one; one] = false.
Proof.
  unfold accept_string.
  rewrite run_from_initial.
  simpl.
  unfold delta.
  simpl.
  reflexivity.
Qed.

(** * Deterministic Properties *)

(**
 * Execution is deterministic
 *)
Theorem run_deterministic :
  forall (s : AutomatonState) (input : PhiString) (s1 s2 : AutomatonState),
    run_automaton s input = s1 ->
    run_automaton s input = s2 ->
    s1 = s2.
Proof.
  intros s input s1 s2 H1 H2.
  rewrite H1 in H2.
  exact H2.
Qed.

(** * Computational Examples *)

(**
 * Test automaton on various patterns
 *)
Example automaton_examples :
  accept_string [] = true /\
  accept_string [zero] = true /\
  accept_string [one] = true /\
  accept_string [zero; one] = true /\
  accept_string [one; zero] = true /\
  accept_string [zero; zero] = true /\
  accept_string [one; one] = false /\
  accept_string [zero; one; one] = false /\
  accept_string [one; zero; one] = true.
Proof.
  repeat split; reflexivity.
Qed.

(** * Module Interface *)

(**
 * Export core execution interface
 *)
Module AutomatonRunInterface.
  Definition exported_run_automaton := run_automaton.
  Definition exported_accept_string := accept_string.
  Definition exported_run_empty_preserves_state := run_empty_preserves_state.
  Definition exported_run_single_bit := run_single_bit.
  Definition exported_run_concatenation := run_concatenation.
  Definition exported_rejection_propagates := rejection_propagates.
  Definition exported_accept_empty_string := accept_empty_string.
  Definition exported_accept_single_bits := accept_single_bits.
  Definition exported_reject_eleven_pattern := reject_eleven_pattern.
  Definition exported_run_deterministic := run_deterministic.
  Definition exported_automaton_examples := automaton_examples.
End AutomatonRunInterface.

End AutomatonRun.

(**
 * Module Summary:
 * 
 * This AutomatonRun module provides the atomic execution function
 * for the φ-language recognition automaton.
 * 
 * Key Achievements:
 * ✓ Single focus: Execution function only
 * ✓ Complete execution: Handles arbitrary input strings
 * ✓ Compositional: Proven concatenation law
 * ✓ Deterministic: Unique execution results
 * ✓ Correct rejection: Properly rejects "11" patterns
 * 
 * This atomic module provides the foundation for:
 * - φ-language membership testing
 * - String validation algorithms
 * - Automaton correctness proofs
 * - All higher-level recognition operations
 *)

(** End of AutomatonRun module *)