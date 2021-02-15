Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import bedrock2.Syntax.
Require Import Rewriter.Language.Wf.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Common.Types.
Require Import Crypto.Bedrock.Field.Common.Names.VarnameGenerator.
Require Import Crypto.Bedrock.Field.Synthesis.Generic.Signature.
Require Import Crypto.Bedrock.Field.Translation.Parameters.Defaults.
Require Import Crypto.Bedrock.Field.Translation.Proofs.Func.
Require Import Crypto.BoundsPipeline.
Require Import Crypto.COperationSpecifications.
Require Import Crypto.PushButtonSynthesis.UnsaturatedSolinas.
Require Import Crypto.Language.API.
Require Import Crypto.UnsaturatedSolinasHeuristics.
Import ListNotations API.Compilers Types.Notations.
Import Language.Wf.Compilers.

Record computed_op
      {p : Types.parameters} {t}
      {op : Pipeline.ErrorT (API.Expr t)}
      {name : String.string}
      {insizes outsizes inlengths}
  :=
  { res : API.Expr t;
    b2_func : func;
    res_eq : op = ErrorT.Success res;
    func_eq :
      b2_func = make_bedrock_func
                  name insizes outsizes inlengths res;
  }.
Global Arguments computed_op {_} {_}.

Class unsaturated_solinas_ops
           {p : Types.parameters}
           {field_parameters : FieldParameters}
           {n s c machine_wordsize} : Type :=
  { mul_op :
      computed_op
        (UnsaturatedSolinas.carry_mul n s c machine_wordsize) Field.mul
        list_binop_insizes list_binop_outsizes (list_binop_inlengths n);
    add_op :
      computed_op
        (UnsaturatedSolinas.add n s c machine_wordsize) Field.add
        list_binop_insizes list_binop_outsizes (list_binop_inlengths n);
    sub_op :
      computed_op
        (UnsaturatedSolinas.sub n s c machine_wordsize) Field.sub
        list_binop_insizes list_binop_outsizes (list_binop_inlengths n);
    opp_op :
      computed_op
        (UnsaturatedSolinas.opp n s c machine_wordsize) Field.opp
        list_unop_insizes list_unop_outsizes (list_unop_inlengths n);
    square_op :
      computed_op
        (UnsaturatedSolinas.carry_square n s c machine_wordsize)
        Field.square
        list_unop_insizes list_unop_outsizes (list_unop_inlengths n);
    scmula24_op :
      computed_op
        (UnsaturatedSolinas.carry_scmul_const n s c Semantics.width
                                              (F.to_Z a24)) Field.scmula24
        list_unop_insizes list_unop_outsizes (list_unop_inlengths n);
    from_bytes_op :
      computed_op
        (UnsaturatedSolinas.from_bytes n s c Semantics.width)
        Field.from_bytes
        from_bytes_insizes from_bytes_outsizes (from_bytes_inlengths
                                                  (n_bytes s));
    to_bytes_op :
      computed_op
        (UnsaturatedSolinas.to_bytes n s c Semantics.width)
        Field.to_bytes
        to_bytes_insizes to_bytes_outsizes (to_bytes_inlengths n);
  }.
Arguments unsaturated_solinas_ops {_ _} _ _ _ _.

Ltac make_computed_op :=
  eapply Build_computed_op;
  lazymatch goal with
  | |- _ = ErrorT.Success _ => vm_compute; reflexivity
  | _ => idtac
  end;
  vm_compute; reflexivity.

Section UnsaturatedSolinas.
  Context {p:Types.parameters} {p_ok : Types.ok}
          {field_parameters : FieldParameters}
          (varname_gen_is_default :
             varname_gen = default_varname_gen).

  Context (n : nat) (s : Z) (c : list (Z * Z))
          (M_eq : M = m s c)
          (check_args_ok :
             check_args n s c Semantics.width (ErrorT.Success tt)
             = ErrorT.Success tt)
          (* TODO: is this proven elsewhere/can it be proven in general? *)
          (tight_bounds_tighter_than:
             list_Z_tighter_than (tight_bounds n s c)
                                 (MaxBounds.max_bounds n))
          (loose_bounds_tighter_than:
             list_Z_tighter_than (loose_bounds n s c)
                                 (MaxBounds.max_bounds n)).
  Context (ops : unsaturated_solinas_ops n s c Semantics.width)
          mul_func add_func sub_func opp_func square_func
          scmula24_func from_bytes_func to_bytes_func
          (mul_func_eq : mul_func = b2_func mul_op)
          (add_func_eq : add_func = b2_func add_op)
          (sub_func_eq : sub_func = b2_func sub_op)
          (opp_func_eq : opp_func = b2_func opp_op)
          (square_func_eq : square_func = b2_func square_op)
          (scmula24_func_eq : scmula24_func = b2_func scmula24_op)
          (from_bytes_func_eq : from_bytes_func = b2_func from_bytes_op)
          (to_bytes_func_eq : to_bytes_func = b2_func to_bytes_op).
  Existing Instance semantics_ok.

  Local Notation weight :=
    (ModOps.weight (QArith_base.Qnum (limbwidth n s c))
                   (Z.pos (QArith_base.Qden (limbwidth n s c))))
      (only parsing).
  (* Note: annoyingly, prime_bytes_bounds is an option type, unlike loose_bounds
     or tight_bounds, so we have to reconstruct it to match list_Z_bounded_by *)
  Local Notation prime_bytes_bounds_value :=
    (map (fun v : Z => Some {| ZRange.lower := 0; ZRange.upper := v |})
         (prime_bytes_upperbound_list s)).
  Local Instance field_representation : FieldRepresentation
    := field_representation
         n (n_bytes s) weight
         (UnsaturatedSolinasHeuristics.loose_bounds n s c)
         (UnsaturatedSolinasHeuristics.tight_bounds n s c)
         (prime_bytes_bounds_value).

  Local Ltac specialize_correctness_hyp Hcorrect :=
    cbv [feval bounded_by bytes_in_bounds field_representation
               Signature.field_representation
               Representation.frep
               Representation.eval_words] in *;
    lazymatch type of Hcorrect with
    | forall x y, ?Px x -> ?Py y -> _ /\ _ =>
      match goal with
        | Hx : Px ?x, Hy : Py ?y |- _ =>
          specialize (Hcorrect x y Hx Hy)
      end
    | forall x, ?Px x -> _ /\ _ =>
      match goal with
        | Hx : Px ?x |- _ =>
          specialize (Hcorrect x Hx)
      end
    end.

  Lemma loose_bounds_eq : Field.loose_bounds = loose_bounds n s c.
  Proof. reflexivity. Qed.
  Lemma tight_bounds_eq : Field.tight_bounds = tight_bounds n s c.
  Proof. reflexivity. Qed.

  (* TODO: could be moved to util *)
  Lemma tighter_than_if_upper_bounded_by lo uppers bs :
    list_Z_bounded_by bs uppers ->
    Forall (fun b =>
              exists r,
                b = Some r /\ ZRange.lower r = lo) bs ->
    list_Z_tighter_than
      (map (fun v : Z => Some {| ZRange.lower := lo; ZRange.upper := v |})
           uppers) bs.
  Proof.
    clear; revert bs; induction uppers; intros;
      lazymatch goal with
      | H : list_Z_bounded_by _ _ |- _ =>
        pose proof H; apply length_list_Z_bounded_by in H
      end; (destruct bs; cbn [length] in *; try auto with lia); [ ].
    repeat lazymatch goal with
           | H : list_Z_bounded_by (_::_) (_::_) |- _ =>
             rewrite Util.list_Z_bounded_by_cons in H
           | |- list_Z_tighter_than (map _ (_ :: _)) (_ :: _) =>
             cbn [map]; rewrite Util.list_Z_tighter_than_cons
           | H : Forall _ (_ :: _) |- _ => inversion H; clear H; subst
           | H : exists _, _ |- _ => destruct H; subst
           | H : _ /\ _ |- _ => destruct H; subst
           end.
    Check Util.list_Z_bounded_by_cons.
    cbv [list_Z_tighter_than].
    Search FoldBool.fold_andb_map.
  Qed.
  Lemma byte_bounds_tighter_than :
    list_Z_tighter_than prime_bytes_bounds_value
                        (ByteBounds.byte_bounds (n_bytes s)).
  Proof.
    clear. cbv [prime_bytes_upperbound_list].
    pose proof
         (ByteBounds.partition_bounded_by (n_bytes s) (s - 1)).
    match goal with
    | H : list_Z_bounded_by ?x ?y |- _ =>
      generalize dependent y; generalize dependent x
    end.
    generalize (
    cbv [list_Z_bounded_by list_Z_tighter_than] in *.
    
    Search FoldBool.fold_andb_map.
    Search list_Z_tighter_than.
    list_Z_bounded_by.
    Search Partition.Partition.partition.
  Qed.

  Local Hint Resolve
        relax_correct func_eq
        inname_gen_varname_gen_disjoint
        outname_gen_varname_gen_disjoint
        length_tight_bounds length_loose_bounds
    : helpers.

  Lemma mul_func_correct :
    valid_func (res mul_op _) ->
    expr.Wf3 (res mul_op) ->
    forall functions,
      spec_of_mul (mul_func :: functions).
  Proof.
    intros. cbv [spec_of_mul]. rewrite mul_func_eq.
    pose proof carry_mul_correct
         _ _ _ _ ltac:(eassumption) _ (res_eq mul_op)
      as Hcorrect.

    eapply list_binop_correct with (res:=res mul_op);
      rewrite ?varname_gen_is_default;
      rewrite ?tight_bounds_eq, ?loose_bounds_eq;
      eauto with helpers; [ | ].
    { (* output *value* is correct *)
      intros. cbv [Solinas.carry_mul_correct expr.Interp] in Hcorrect.
      specialize_correctness_hyp Hcorrect.
      destruct Hcorrect as [Heq Hbounds].
      rewrite Util.map_unsigned_of_Z.
      rewrite (MaxBounds.map_word_wrap_bounded) with (n0:=n)
        by eauto using relax_list_Z_bounded_by.
      apply F.eq_of_Z_iff. rewrite !F.to_Z_of_Z.
      cbv [M] in M_eq. rewrite M_eq, Heq.
      Modulo.pull_Zmod; reflexivity. }
    { (* output *bounds* are correct *)
      intros. cbv [Solinas.carry_mul_correct] in Hcorrect.
      apply Hcorrect; auto. }
  Qed.

  Lemma add_func_correct :
    valid_func (res add_op _) ->
    expr.Wf3 (res add_op) ->
    forall functions,
      spec_of_add (add_func :: functions).
  Proof.
    intros. cbv [spec_of_add]. rewrite add_func_eq.
    pose proof add_correct
         _ _ _ _ ltac:(eassumption) _ (res_eq add_op)
      as Hcorrect.

    eapply list_binop_correct with (res:=res add_op);
      rewrite ?varname_gen_is_default;
      rewrite ?tight_bounds_eq, ?loose_bounds_eq;
      eauto with helpers; [ | ].
    { (* output *value* is correct *)
      intros. cbv [Solinas.add_correct expr.Interp] in Hcorrect.
      specialize_correctness_hyp Hcorrect.
      destruct Hcorrect as [Heq Hbounds].
      rewrite Util.map_unsigned_of_Z.
      rewrite (MaxBounds.map_word_wrap_bounded) with (n0:=n)
        by eauto using relax_list_Z_bounded_by.
      apply F.eq_of_Z_iff. rewrite !F.to_Z_of_Z.
      cbv [M] in M_eq. rewrite M_eq, Heq.
      Modulo.pull_Zmod; reflexivity. }
    { (* output *bounds* are correct *)
      intros. cbv [Solinas.add_correct] in Hcorrect.
      apply Hcorrect; auto. }
  Qed.

  Lemma opp_func_correct :
    valid_func (res opp_op _) ->
    expr.Wf3 (res opp_op) ->
    forall functions,
      spec_of_opp (opp_func :: functions).
  Proof.
    intros. cbv [spec_of_opp]. rewrite opp_func_eq.
    pose proof opp_correct
         _ _ _ _ ltac:(eassumption) _ (res_eq opp_op)
      as Hcorrect.

    eapply list_unop_correct with (res:=res opp_op);
      rewrite ?varname_gen_is_default;
      rewrite ?tight_bounds_eq, ?loose_bounds_eq;
      eauto with helpers; [ | ].
    { (* output *value* is correct *)
      intros. cbv [Solinas.opp_correct expr.Interp] in Hcorrect.
      specialize_correctness_hyp Hcorrect.
      destruct Hcorrect as [Heq Hbounds].
      rewrite Util.map_unsigned_of_Z.
      rewrite (MaxBounds.map_word_wrap_bounded) with (n0:=n)
        by eauto using relax_list_Z_bounded_by.
      apply F.eq_of_Z_iff. rewrite !F.to_Z_of_Z.
      cbv [M] in M_eq. rewrite M_eq, Heq.
      Modulo.pull_Zmod; reflexivity. }
    { (* output *bounds* are correct *)
      intros. cbv [Solinas.opp_correct] in Hcorrect.
      apply Hcorrect; auto. }
  Qed.

  Lemma from_bytes_func_correct :
    valid_func (res from_bytes_op _) ->
    expr.Wf3 (res from_bytes_op) ->
    forall functions,
      spec_of_from_bytes (from_bytes_func :: functions).
  Proof.
    intros. cbv [spec_of_from_bytes]. rewrite from_bytes_func_eq.
    pose proof UnsaturatedSolinas.from_bytes_correct
         _ _ _ _ ltac:(eassumption) _ (res_eq from_bytes_op)
      as Hcorrect.

    eapply Signature.from_bytes_correct with (res:=res from_bytes_op);
      rewrite ?varname_gen_is_default;
      rewrite ?tight_bounds_eq, ?loose_bounds_eq;
      eauto with helpers; [ | ].
    { (* output *value* is correct *)
      intros. cbv [Solinas.from_bytes_correct expr.Interp] in Hcorrect.
      (* simplify bounds expression *)
      match type of Hcorrect with
      | context [list_Z_bounded_by (map ?f ?x)] =>
        change (map f x) with prime_bytes_bounds_value in Hcorrect
      end.
      specialize_correctness_hyp Hcorrect.
      destruct Hcorrect as [Heq Hbounds].
      rewrite Util.map_unsigned_of_Z.
      rewrite (MaxBounds.map_word_wrap_bounded) with (n0:=n)
        by eauto using relax_list_Z_bounded_by.
      apply F.eq_of_Z_iff.
      cbv [M] in M_eq. rewrite M_eq.
      rewrite Heq. reflexivity. }
    { (* output *bounds* are correct *)
      intros. cbv [Solinas.from_bytes_correct] in Hcorrect.
      apply Hcorrect; auto. }
  Qed.

  Lemma to_bytes_func_correct :
    valid_func (res to_bytes_op _) ->
    expr.Wf3 (res to_bytes_op) ->
    forall functions,
      spec_of_to_bytes (to_bytes_func :: functions).
  Proof.
    intros. cbv [spec_of_to_bytes]. rewrite to_bytes_func_eq.
    pose proof UnsaturatedSolinas.to_bytes_correct
         _ _ _ _ ltac:(eassumption) _ (res_eq to_bytes_op)
      as Hcorrect.

    eapply Signature.to_bytes_correct with (res:=res to_bytes_op);
      rewrite ?varname_gen_is_default;
      rewrite ?tight_bounds_eq, ?loose_bounds_eq;
      eauto with helpers.
    Print HintDb helpers.
    [ | ].
    { (* output *value* is correct *)
      intros. cbv [Solinas.to_bytes_correct expr.Interp] in Hcorrect.
      (* simplify bounds expression *)
      match type of Hcorrect with
      | context [list_Z_bounded_by (map ?f ?x)] =>
        change (map f x) with prime_bytes_bounds_value in Hcorrect
      end.
      specialize_correctness_hyp Hcorrect.
      destruct Hcorrect as [Heq Hbounds].
      rewrite Util.map_unsigned_of_Z.
      rewrite (MaxBounds.map_word_wrap_bounded) with (n0:=n)
        by eauto using relax_list_Z_bounded_by.
      apply F.eq_of_Z_iff.
      cbv [M] in M_eq. rewrite M_eq.
      rewrite Heq. reflexivity. }
    { (* output *bounds* are correct *)
      intros. cbv [Solinas.to_bytes_correct] in Hcorrect.
      apply Hcorrect; auto. }
  Qed.

End UnsaturatedSolinas.

(* Prototyping full pipeline: *)

Require Import Coq.Strings.String.
Require Import Crypto.Bedrock.Field.Translation.Parameters.Defaults64.
Require Import Crypto.Bedrock.Field.Translation.Proofs.ValidComputable.Func.

(* TODO: move somewhere common *)
Definition field_parameters_prefixed
           M_pos a24 (prefix: string) : FieldParameters :=
  Build_FieldParameters
    M_pos a24
    (prefix ++ "mul")
    (prefix ++ "add")
    (prefix ++ "sub")
    (prefix ++ "opp")
    (prefix ++ "square")
    (prefix ++ "scmula24")
    (prefix ++ "inv")
    (prefix ++ "from_bytes")
    (prefix ++ "to_bytes")
    (prefix ++ "copy")
    (prefix ++ "small_literal")
.

Local Ltac begin_derive_bedrock2_func :=
  lazymatch goal with
  | |- context [spec_of_mul] => eapply mul_func_correct
  | |- context [spec_of_add] => eapply add_func_correct
  | |- context [spec_of_opp] => eapply opp_func_correct
  | |- context [spec_of_from_bytes] => eapply from_bytes_func_correct
  end.

Local Ltac derive_bedrock2_func op :=
  begin_derive_bedrock2_func;
  (* this goal fills in the evar, so do it first for [abstract] to be happy *)
  try lazymatch goal with
      | |- _ = b2_func _ => vm_compute; reflexivity
      end;
  (* solve all the remaining goals *)
  lazymatch goal with
  | |- _ = @ErrorT.Success ?ErrT unit tt =>
    abstract (vm_cast_no_check (@eq_refl _ (@ErrorT.Success ErrT unit tt)))
  | |- list_Z_tighter_than _ _ =>
    abstract (vm_cast_no_check (@eq_refl bool true))
  | |- valid_func _ =>
    eapply valid_func_bool_iff;
    abstract vm_cast_no_check (eq_refl true)
  | |- expr.Wf3 _ => abstract (prove_Wf3 ()) (* this abstract is slow, but if it is removed the slowness moves to Qed instead *)
  | |- _ = m _ _ => vm_compute; reflexivity
  | |- _ = default_varname_gen => vm_compute; reflexivity
  end.

Section Tests.
  Definition n := 5%nat.
  Definition s := (2^255)%Z.
  Definition c := [(1, 19)]%Z.

  Existing Instances default_parameters default_parameters_ok semantics semantics_ok.
  Existing Instances no_select_size split_mul_to split_multiret_to.
  Instance machine_wordsize_opt : machine_wordsize_opt := machine_wordsize.

  Definition prefix : string := "fe25519_"%string.

  Instance field_parameters : FieldParameters.
  Proof.
    let M := (eval vm_compute in (Z.to_pos (m s c))) in
    let a := constr:(F.of_Z M 486662) in
    let prefix := constr:("fe25519_"%string) in
    eapply
      (field_parameters_prefixed
         M ((a - F.of_Z _ 2) / F.of_Z _ 4)%F prefix).
  Defined.

  Instance fe25519_ops : unsaturated_solinas_ops n s c machine_wordsize.
  Proof. Time constructor; make_computed_op. Defined.

  Derive fe25519_mul
         SuchThat (forall functions,
                      spec_of_mul
                        (field_representation:=field_representation n s c)
                        (fe25519_mul :: functions))
         As fe25519_mul_correct.
  Proof. Time derive_bedrock2_func mul_op. Qed.

  Derive fe25519_add
         SuchThat (forall functions,
                      spec_of_add
                        (field_representation:=field_representation n s c)
                        (fe25519_add :: functions))
         As fe25519_add_correct.
  Proof. Time derive_bedrock2_func add_op. Qed.

  Derive fe25519_opp
         SuchThat (forall functions,
                      spec_of_opp
                        (field_representation:=field_representation n s c)
                        (fe25519_opp :: functions))
         As fe25519_opp_correct.
  Proof. Time derive_bedrock2_func opp_op. Qed.

  Derive fe25519_from_bytes
         SuchThat (forall functions,
                      spec_of_from_bytes
                        (field_representation:=field_representation n s c)
                        (fe25519_from_bytes :: functions))
         As fe25519_from_bytes_correct.
  Proof. Time derive_bedrock2_func from_bytes_op. Qed.
End Tests.

Print fe25519_add.
Print fe25519_opp.
Print fe25519_from_bytes.
(* Current status: mul/add/opp/from_bytes prototyped through full pipeline
   Done:
   - fix from_bytes proof in Signature.v
   - prototype from_bytes through full pipeline
   Next:
   - prototype to_bytes through full pipeline
   - add remaining operations using existing Signature lemmas
   - wbw montgomery
   - replace old pipeline with new
*)