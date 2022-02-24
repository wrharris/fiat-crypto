Require Import Coq.ZArith.ZArith.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Syntax.
Require Import compiler.Pipeline.
Require Import compiler.MMIO.
Require Import coqutil.Map.SortedListWord.
Require Import coqutil.Map.Z_keyed_SortedListMap.
Require Import coqutil.Word.Bitwidth32.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.End2End.X25519.Field25519.
Require Import Crypto.Bedrock.End2End.X25519.MontgomeryLadder.
Require Import Crypto.Bedrock.Field.Synthesis.New.UnsaturatedSolinas.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Interface.Compilation2.
Require Import Crypto.Bedrock.Group.ScalarMult.MontgomeryLadder.

Local Arguments map.rep: clear implicits.

Definition montladder_insns := fst (fst montladder_compiler_result).
Definition montladder_finfo := snd (fst montladder_compiler_result).
Definition montladder_stack_size := snd montladder_compiler_result.

Definition fname := fst montladder.
Definition argnames := fst (fst (snd montladder)).
Definition retnames := snd (fst (snd montladder)).
Definition fbody := snd (snd montladder).
Definition f_rel_pos : Z.
  let x := constr:(map.get montladder_finfo fname) in
  let y := eval vm_compute in x in
  match y with
  | Some (_, ?pos) => exact pos
  end.
Defined.

Local Instance mem : map.map (word.rep (width:=32)) Init.Byte.byte := SortedListWord.map _ _.
Local Existing Instance BW32.

(* scalars are 253 bits long *)
Definition scalarbits : nat := 253.

(* Postcondition extracted from spec_of_montladder *)
Definition montladder_post (pOUT pK pU : word.rep (word:=BasicC32Semantics.word))
          (Kbytes : list Byte.byte) (K : Z)
          (U : F (Field.M_pos (FieldParameters:=field_parameters)))
          (OUT : F (Field.M_pos (FieldParameters:=field_parameters)))
          (R : map.rep word.rep Init.Byte.byte mem -> Prop)
          (tr : Semantics.trace) :
  Semantics.trace -> map.rep _ _ mem -> list (word.rep (word:=BasicC32Semantics.word)) -> Prop :=
   (fun (tr' : Semantics.trace)
        (mem' : map.rep word.rep Init.Byte.byte mem)
        (rets : list word.rep) =>
      rets = [] /\
      tr' = tr /\
      (FElem
         (BW:=BW32)
         (field_representaton:=field_representation n s c)
         (Some Field.tight_bounds) pOUT
         (montladder_gallina Field.M_pos Field.a24 scalarbits K U)
         ⋆ Array.array ptsto (word.of_Z 1) pK Kbytes
         ⋆ FElem (BW:=BW32)
                 (field_representaton:=field_representation n s c)
                 (Some Field.tight_bounds) pU U ⋆ R)%sep
        mem').

Local Instance Registers : map.map Z (@word.rep 32 BasicC32Semantics.word)
  := Zkeyed_map _.

Lemma montladder_compiles_correctly :
  forall (t : Semantics.trace)
         (mH : map.rep word.rep Init.Byte.byte mem)
         (pOUT pK pU : word.rep) (out_bound : option Field.bounds)
         (OUT U: F Field.M_pos) (Kbytes : list Byte.byte) (K : Z)
         (initial : MetricRiscvMachine)
         (stack_lo stack_hi ret_addr p_funcs : word.rep)
         (R Rdata Rexec : map.rep word.rep Init.Byte.byte mem -> Prop),
         LittleEndianList.le_combine Kbytes = K ->
         length Kbytes = 32%nat ->
         (FElem (BW:=BW32)
                (field_representaton:=field_representation n s c)
                out_bound pOUT OUT
          ⋆ Array.array ptsto (word.of_Z 1) pK Kbytes
          ⋆  FElem (BW:=BW32)
                   (field_representaton:=field_representation n s c)
                   (Some Field.tight_bounds) pU U
          ⋆ R)%sep mH ->
         montladder_stack_size <=
         word.unsigned (word.sub stack_hi stack_lo) /
         SeparationLogic.bytes_per_word ->
         word.unsigned (word.sub stack_hi stack_lo)
         mod SeparationLogic.bytes_per_word = 0 ->
         getPc (getMachine initial) = word.add p_funcs (word.of_Z f_rel_pos) ->
         map.get (getRegs (getMachine initial)) RegisterNames.ra =
         Some ret_addr ->
         word.unsigned ret_addr mod 4 = 0 ->
         map.getmany_of_list (getRegs (getMachine initial))
           (firstn (Datatypes.length argnames) (reg_class.all reg_class.arg)) =
         Some [pOUT; pK; pU] ->
         getLog (getMachine initial) = t ->
         LowerPipeline.machine_ok p_funcs stack_lo stack_hi montladder_insns
           mH Rdata Rexec initial ->
         FlatToRiscvCommon.runsTo initial
           (fun final : MetricRiscvMachine =>
            exists
              (mH' : map.rep word.rep Init.Byte.byte mem)
            (retvals : list word.rep),
              map.getmany_of_list (getRegs (getMachine final))
                (firstn (Datatypes.length retnames)
                   (reg_class.all reg_class.arg)) =
              Some retvals /\
              montladder_post pOUT pK pU Kbytes K U OUT R t
                 (getLog (getMachine final)) mH' retvals /\
              map.agree_on LowerPipeline.callee_saved
                (getRegs (getMachine initial)) (getRegs (getMachine final)) /\
              getPc (getMachine final) = ret_addr /\
              LowerPipeline.machine_ok p_funcs stack_lo stack_hi
                montladder_insns mH' Rdata Rexec final).
Proof.
Admitted.
