(***************************************************)
(* Copyright 2008 Jean-Christophe Filliâtre        *)
(* Copyright 2008-2012 Guillaume Melquiond         *)
(*                                                 *)
(* This file is distributed under the terms of the *)
(* GNU Lesser General Public License Version 2.1   *)
(***************************************************)

open Format
open Util
open Pp
open Term
open Tacmach
open Names
open Coqlib
open Libnames
open Evarutil

let debug = ref false

(* 1. gappa syntax trees and output *)

module Constant = struct

  open Bigint

  type t = { mantissa : bigint; base : int; exp : bigint }

  let create (b, m, e) =
    { mantissa = m; base = b; exp = e }

  let of_int x =
    { mantissa = x; base = 1; exp = zero }

  let print fmt x = match x.base with
    | 1 -> fprintf fmt "%s" (to_string x.mantissa)
    | 2 -> fprintf fmt "%sb%s" (to_string x.mantissa) (to_string x.exp)
    | 10 -> fprintf fmt "%se%s" (to_string x.mantissa) (to_string x.exp)
    | _ -> assert false

end

type binop = Bminus | Bplus | Bmult | Bdiv

type unop = Usqrt | Uabs | Uopp

type rounding_mode = string

type term =
  | Tconst of Constant.t
  | Tvar of string
  | Tbinop of binop * term * term
  | Tunop of unop * term
  | Tround of rounding_mode * term

type atom =
  | Ain of term * Constant.t option * Constant.t option
  | Arel of term * term * Constant.t * Constant.t
  | Aeq of term * term

type pred =
  | Patom of atom
  | Pand of pred * pred
  | Por of pred * pred
  | Pnot of pred

(** {1 Symbols needed by the tactics} *)

let logic_dir = ["Coq"; "Logic"; "Decidable"]
let coq_modules =
  init_modules @ [logic_dir] @ arith_modules @ zarith_base_modules
    @ [["Coq"; "ZArith"; "BinInt"];
       ["Coq"; "Reals"; "Rdefinitions"];
       ["Coq"; "Reals"; "Raxioms"];
       ["Coq"; "Reals"; "Rbasic_fun"];
       ["Coq"; "Reals"; "R_sqrt"];
       ["Coq"; "Reals"; "Rfunctions"];
       ["Coq"; "Lists"; "List"];
       ["Gappa"; "Gappa_tactic"];
       ["Gappa"; "Gappa_fixed"];
       ["Gappa"; "Gappa_float"];
       ["Gappa"; "Gappa_round_def"];
       ["Gappa"; "Gappa_pred_bnd"];
       ["Gappa"; "Gappa_definitions"];
       ["Flocq"; "Core"; "Fcore_Zaux"];
       ["Flocq"; "Core"; "Fcore_Raux"];
       ["Flocq"; "Core"; "Fcore_generic_fmt"];
       ["Flocq"; "Core"; "Fcore_FLT"];
       ["Flocq"; "Core"; "Fcore_FIX"];
  ]

let constant = gen_constant_in_modules "gappa" coq_modules

let coq_True = lazy (constant "True")
let coq_False = lazy (constant "False")
let coq_eq = lazy (build_coq_eq ())
let coq_refl_equal = lazy (constant "refl_equal")

let coq_and = lazy (constant "and")
let coq_or = lazy (constant "or")
let coq_not = lazy (constant "not")

let coq_R = lazy (constant "R")
let coq_R0 = lazy (constant "R0")
let coq_R1 = lazy (constant "R1")
let coq_Rle = lazy (constant "Rle")
let coq_Rge = lazy (constant "Rge")

let coq_Rplus = lazy (constant "Rplus")
let coq_Rminus = lazy (constant "Rminus")
let coq_Ropp = lazy (constant "Ropp")
let coq_Rmult = lazy (constant "Rmult")
let coq_Rdiv = lazy (constant "Rdiv")
let coq_Rinv = lazy (constant "Rinv")
let coq_Rabs = lazy (constant "Rabs")
let coq_sqrt = lazy (constant "R_sqrt.sqrt")
let coq_powerRZ = lazy (constant "powerRZ")
let coq_bpow = lazy (constant "bpow")

let coq_INR = lazy (constant "INR")
let coq_IZR = lazy (constant "IZR")
let coq_radix_val = lazy (constant "radix_val")

let coq_Some = lazy (constant "Some")

let coq_pair = lazy (constant "pair")

let coq_list = lazy (constant "list")
let coq_cons = lazy (constant "cons")
let coq_nil = lazy (constant "nil")

let coq_convert_tree = lazy (constant "convert_tree")

let coq_RTree = lazy (constant "RTree")
let coq_rtTrue = lazy (constant "rtTrue")
let coq_rtFalse = lazy (constant "rtFalse")
let coq_rtAtom = lazy (constant "rtAtom")
let coq_rtNot = lazy (constant "rtNot")
let coq_rtAnd = lazy (constant "rtAnd")
let coq_rtOr = lazy (constant "rtOr")
let coq_rtImpl = lazy (constant "rtImpl")

let coq_RAtom = lazy (constant "RAtom")
let coq_raBound = lazy (constant "raBound")
let coq_raRel = lazy (constant "raRel")
let coq_raEq = lazy (constant "raEq")
let coq_raLe = lazy (constant "raLe")
let coq_raGeneric = lazy (constant "raGeneric")
let coq_raFormat = lazy (constant "raFormat")

let coq_RExpr = lazy (constant "RExpr")
let coq_reUnknown = lazy (constant "reUnknown")
let coq_reFloat2 = lazy (constant "reFloat2")
let coq_reFloat10 = lazy (constant "reFloat10")
let coq_reBpow2 = lazy (constant "reBpow2")
let coq_reBpow10 = lazy (constant "reBpow10")
let coq_rePow2 = lazy (constant "rePow2")
let coq_rePow10 = lazy (constant "rePow10")
let coq_reINR = lazy (constant "reINR")
let coq_reIZR = lazy (constant "reIZR")
let coq_reInteger = lazy (constant "reInteger")
let coq_reBinary = lazy (constant "reBinary")
let coq_reUnary = lazy (constant "reUnary")
let coq_reRound = lazy (constant "reRound")

let coq_mRndDN = lazy (constant "mRndDN")
let coq_mRndNA = lazy (constant "mRndNA")
let coq_mRndNE = lazy (constant "mRndNE")
let coq_mRndUP = lazy (constant "mRndUP")
let coq_mRndZR = lazy (constant "mRndZR")
let coq_fFloat = lazy (constant "fFloat")
let coq_fFixed = lazy (constant "fFixed")

let coq_rndDN = lazy (constant "Zfloor")
let coq_rndUP = lazy (constant "Zceil")
let coq_rndNE = lazy (constant "rndNE")
let coq_rndNA = lazy (constant "rndNA")
let coq_rndZR = lazy (constant "Ztrunc")
let coq_round = lazy (constant "round")
let coq_FLT_format = lazy (constant "FLT_format")
let coq_FIX_format = lazy (constant "FIX_format")
let coq_FLT_exp = lazy (constant "FLT_exp")
let coq_FIX_exp = lazy (constant "FIX_exp")
let coq_generic_format = lazy (constant "generic_format")

let coq_boAdd = lazy (constant "boAdd")
let coq_boSub = lazy (constant "boSub")
let coq_boMul = lazy (constant "boMul")
let coq_boDiv = lazy (constant "boDiv")
let coq_uoAbs = lazy (constant "uoAbs")
let coq_uoNeg = lazy (constant "uoNeg")
let coq_uoInv = lazy (constant "uoInv")
let coq_uoSqrt = lazy (constant "uoSqrt")

let coq_bool = lazy (constant "bool")
let coq_true = lazy (constant "true")
let coq_false = lazy (constant "false")

let coq_O = lazy (constant "O")
let coq_S = lazy (constant "S")

let coq_Z0 = lazy (constant "Z0")
let coq_Zpos = lazy (constant "Zpos")
let coq_Zneg = lazy (constant "Zneg")
let coq_xH = lazy (constant "xH")
let coq_xI = lazy (constant "xI")
let coq_xO = lazy (constant "xO")

(** {1 Reification from Coq user goal: the [gappa_quote] tactic} *)

exception NotGappa of constr

let var_table = Hashtbl.create 17
let var_list = ref []
let global_env = ref Environ.empty_env

let mkLApp f v = mkApp (Lazy.force f, v)

let mkList t =
  List.fold_left (fun acc v -> mkLApp coq_cons [|t; v; acc|]) (mkLApp coq_nil [|t|])

let rec mk_pos n =
  if n = 1 then Lazy.force coq_xH
  else if n land 1 = 0 then mkLApp coq_xO [|mk_pos (n / 2)|]
  else mkLApp coq_xI [|mk_pos (n / 2)|]

type int_type = It_1 | It_2 | It_even of constr | It_int of constr | It_none of constr
type int_type_partial = Itp_1 | Itp_2 | Itp_even of int | Itp_int of int

(** translate a closed Coq term [p:positive] into [int] *)
let rec tr_positive p = match kind_of_term p with
  | Term.Construct _ when p = Lazy.force coq_xH -> 1
  | Term.App (f, [|a|]) when f = Lazy.force coq_xI -> 2 * (tr_positive a) + 1
  | Term.App (f, [|a|]) when f = Lazy.force coq_xO -> 2 * (tr_positive a)
  | Term.Cast (p, _, _) -> tr_positive p
  | _ -> raise (NotGappa p)

(** translate a closed Coq term [t:Z] into [int] *)
let rec tr_arith_constant t = match kind_of_term t with
  | Term.Construct _ when t = Lazy.force coq_Z0 -> 0
  | Term.App (f, [|a|]) when f = Lazy.force coq_Zpos -> tr_positive a
  | Term.App (f, [|a|]) when f = Lazy.force coq_Zneg -> - (tr_positive a)
  | Term.Cast (t, _, _) -> tr_arith_constant t
  | _ -> raise (NotGappa t)

(** translate a closed Coq term [t:R] into [int] *)
let tr_real_constant t =
  let rec aux t =
    match decompose_app t with
      | c, [] when c = Lazy.force coq_R1 -> Itp_1
      | c, [a;b] ->
          if c = Lazy.force coq_Rplus then
            if aux a = Itp_1 then
              match aux b with
                | Itp_1 -> Itp_2
                | Itp_2 -> Itp_int 3
                | Itp_even n -> Itp_int (2 * n + 1)
                | _ -> raise (NotGappa t)
            else
              raise (NotGappa t)
          else if c = Lazy.force coq_Rmult then
            if aux a = Itp_2 then
              match aux b with
                | Itp_2 -> Itp_even 2
                | Itp_even n -> Itp_even (2 * n)
                | Itp_int n -> Itp_even n
                | _ -> raise (NotGappa t)
            else
              raise (NotGappa t)
          else
            raise (NotGappa t)
      | _ ->
        raise (NotGappa t)
    in
  match aux t with
    | Itp_1 -> 1
    | Itp_2 -> 2
    | Itp_even n -> 2 * n
    | Itp_int n -> n

(** create a term of type [Z] from a quoted real (supposedly constant) *)
let plain_of_int =
  let wrap t =
    mkLApp coq_reInteger [|mkLApp coq_Zpos [|t|]|] in
  function
    | It_1 -> wrap (Lazy.force coq_xH)
    | It_2 -> wrap (mkLApp coq_xO [|Lazy.force coq_xH|])
    | It_even n -> wrap (mkLApp coq_xO [|n|])
    | It_int n -> wrap n
    | It_none n -> n

(** reify a format [Z->Z] *)
let qt_fmt f =
  match decompose_app f with
    | c, [e;p] when c = Lazy.force coq_FLT_exp -> mkLApp coq_fFloat [|e;p|]
    | c, [e] when c = Lazy.force coq_FIX_exp -> mkLApp coq_fFixed [|e|]
    | _ -> raise (NotGappa f)

(** reify a Coq term [t:R] *)
let rec qt_term t =
  plain_of_int (qt_Rint t)
and qt_Rint t =
  match decompose_app t with
    | c, [] when c = Lazy.force coq_R1 -> It_1
    | c, [a;b] ->
        if c = Lazy.force coq_Rplus then
          let a = qt_Rint a in
          if a = It_1 then
            match qt_Rint b with
              | It_1 -> It_2
              | It_2 -> It_int (mkLApp coq_xI [|Lazy.force coq_xH|])
              | It_even n -> It_int (mkLApp coq_xI [|n|])
              | (It_int n) as b ->
                  It_none (mkLApp coq_reBinary
                    [|Lazy.force coq_boAdd; plain_of_int a; plain_of_int b|])
              | It_none e ->
                  It_none (mkLApp coq_reBinary
                    [|Lazy.force coq_boAdd; plain_of_int a; e|])
          else
            It_none (mkLApp coq_reBinary
              [|Lazy.force coq_boAdd; plain_of_int a; qt_term b|])
        else if c = Lazy.force coq_Rmult then
          let a = qt_Rint a in
          if a = It_2 then
            match qt_Rint b with
              | It_2 -> It_even (mkLApp coq_xO [|Lazy.force coq_xH|])
              | It_even n -> It_even (mkLApp coq_xO [|n|])
              | It_int n -> It_even n
              | _ as b ->
                  It_none (mkLApp coq_reBinary
                    [|Lazy.force coq_boMul; plain_of_int a; plain_of_int b|])
          else
            It_none (mkLApp coq_reBinary
              [|Lazy.force coq_boMul; plain_of_int a; qt_term b|])
        else
          It_none (qt_no_Rint t)
    | _ ->
      It_none (qt_no_Rint t)
and qt_no_Rint t =
  try
    match decompose_app t with
      | c, [] when c = Lazy.force coq_R0 ->
        mkLApp coq_reInteger [|Lazy.force coq_Z0|]
      | c, [a] ->
        begin
          let gen_un f = mkLApp coq_reUnary [|Lazy.force f; qt_term a|] in
          if c = Lazy.force coq_Ropp then gen_un coq_uoNeg else
          if c = Lazy.force coq_Rinv then gen_un coq_uoInv else
          if c = Lazy.force coq_Rabs then gen_un coq_uoAbs else
          if c = Lazy.force coq_sqrt then gen_un coq_uoSqrt else
          raise (NotGappa t)
        end
      | c, [_;v;w;b] when c = Lazy.force coq_round ->
          (* TODO: check radix *)
          let mode = match decompose_app w with
            | c, [] when c = Lazy.force coq_rndDN -> Lazy.force coq_mRndDN
            | c, [] when c = Lazy.force coq_rndNA -> Lazy.force coq_mRndNA
            | c, [] when c = Lazy.force coq_rndNE -> Lazy.force coq_mRndNE
            | c, [] when c = Lazy.force coq_rndUP -> Lazy.force coq_mRndUP
            | c, [] when c = Lazy.force coq_rndZR -> Lazy.force coq_mRndZR
            | _ -> raise (NotGappa w) in
          mkLApp coq_reRound [|qt_fmt v; mode; qt_term b|]
      | c, [a;b] ->
          let gen_bin f = mkLApp coq_reBinary [|Lazy.force f; qt_term a; qt_term b|] in
          if c = Lazy.force coq_Rminus then gen_bin coq_boSub else
          if c = Lazy.force coq_Rdiv then gen_bin coq_boDiv else
          if c = Lazy.force coq_powerRZ then
            let p =
              match tr_real_constant a with
                | 2 -> coq_rePow2
                | 10 -> coq_rePow10
                | _ -> raise (NotGappa t)
              in
            mkLApp p [|(ignore (tr_arith_constant b); b)|] else
          if c = Lazy.force coq_bpow then
            let p =
              match tr_arith_constant (Tacred.compute !global_env Evd.empty
                (mkLApp coq_radix_val [|a|])) with
                | 2 -> coq_reBpow2
                | 10 -> coq_reBpow10
                | _ -> raise (NotGappa t)
              in
            mkLApp p [|(ignore (tr_arith_constant b); b)|]
          else raise (NotGappa t)
      | _ -> raise (NotGappa t)
  with NotGappa _ ->
    try
      Hashtbl.find var_table t
    with Not_found ->
      let e = mkLApp coq_reUnknown [|mk_pos (Hashtbl.length var_table + 1)|] in
      Hashtbl.replace var_table t e;
      var_list := t :: !var_list;
      e

(** reify a Coq term [p:Prop] *)
let rec qt_pred p = match kind_of_term p with
  | Prod (_,a,b) -> mkLApp coq_rtImpl [|qt_pred a; qt_pred b|]
  | _ ->
match decompose_app p with
  | c, [] when c = Lazy.force coq_True ->
      Lazy.force coq_rtTrue
  | c, [] when c = Lazy.force coq_False ->
      Lazy.force coq_rtFalse
  | c, [a] when c = Lazy.force coq_not ->
      mkLApp coq_rtNot [|qt_pred a|]
  | c, [a;b] when c = Lazy.force coq_and ->
      begin match decompose_app a, decompose_app b with
        | (c1, [a1;b1]), (c2, [a2;b2])
          when c1 = Lazy.force coq_Rle && c2 = Lazy.force coq_Rle && b1 = a2 ->
            mkLApp coq_rtAtom [|mkLApp coq_raBound
              [|mkLApp coq_Some [|Lazy.force coq_RExpr; qt_term a1|]; qt_term b1;
                mkLApp coq_Some [|Lazy.force coq_RExpr; qt_term b2|]|]|]
        | _ ->
            mkLApp coq_rtAnd [|qt_pred a; qt_pred b|]
      end
  | c, [a;b] when c = Lazy.force coq_or ->
      mkLApp coq_rtOr [|qt_pred a; qt_pred b|]
  | c, [a;b] when c = Lazy.force coq_Rle ->
      mkLApp coq_rtAtom [|mkLApp coq_raLe [|qt_term a; qt_term b|]|]
  (*| c, [a;b] when c = Lazy.force coq_Rge ->
      mkLApp coq_rtAtom [|mkLApp coq_raLe [|qt_term b; qt_term a|]|]*)
  | c, [t;a;b] when c = Lazy.force coq_eq && t = Lazy.force coq_R ->
      mkLApp coq_rtAtom [|mkLApp coq_raEq [|qt_term a; qt_term b|]|]
  | c, [_;e;x] when c = Lazy.force coq_FIX_format ->
      let fmt = mkLApp coq_fFixed [|e|] in
      mkLApp coq_rtAtom [|mkLApp coq_raFormat [|fmt; qt_term x|]|]
  | c, [_;e;p;x] when c = Lazy.force coq_FLT_format ->
      let fmt = mkLApp coq_fFloat [|e;p|] in
      mkLApp coq_rtAtom [|mkLApp coq_raFormat [|fmt; qt_term x|]|]
  | c, [_;f;x] when c = Lazy.force coq_generic_format ->
      mkLApp coq_rtAtom [|mkLApp coq_raGeneric [|qt_fmt f; qt_term x|]|]
  | _ -> raise (NotGappa p)

(** reify hypotheses *)
let qt_hyps =
  List.fold_left
    (fun acc (n, h) -> try (n, qt_pred h) :: acc with NotGappa _ -> acc) []

(** the [gappa_quote] tactic *)
let gappa_quote gl =
  try
    global_env := pf_env gl;
    let l = qt_hyps (pf_hyps_types gl) in
    let _R = Lazy.force coq_R in
    let g = List.fold_left
      (fun acc (_, h) -> mkLApp coq_rtImpl [|h; acc|])
      (qt_pred (pf_concl gl)) l in
    let uv = mkList _R !var_list in
    let e = mkLApp coq_convert_tree [|uv; g|] in
    (*Pp.msgerrnl (Printer.pr_constr e);*)
    Hashtbl.clear var_table;
    var_list := [];
    Tacticals.tclTHEN
      (Tacticals.tclTHEN
        (Tactics.generalize (List.map (fun (n, _) -> mkVar n) (List.rev l)))
        (Tactics.keep []))
      (Tacmach.convert_concl_no_check e DEFAULTcast) gl
  with
    | NotGappa t ->
      Hashtbl.clear var_table;
      var_list := [];
      anomalylabstrm "gappa_quote"
        (Pp.str "something wrong happened with term " ++ Printer.pr_constr t)

(** {1 Goal parsing, call to Gappa, and proof building: the [gappa_internal] tactic} *)

(** translate a closed Coq term [p:positive] into [bigint] *)
let rec tr_bigpositive p = match kind_of_term p with
  | Term.Construct _ when p = Lazy.force coq_xH ->
      Bigint.one
  | Term.App (f, [|a|]) when f = Lazy.force coq_xI ->
      Bigint.add_1 (Bigint.mult_2 (tr_bigpositive a))
  | Term.App (f, [|a|]) when f = Lazy.force coq_xO ->
      (Bigint.mult_2 (tr_bigpositive a))
  | Term.Cast (p, _, _) ->
      tr_bigpositive p
  | _ ->
      raise (NotGappa p)

(** translate a closed Coq term [t:Z] into [bigint] *)
let rec tr_arith_bigconstant t = match kind_of_term t with
  | Term.Construct _ when t = Lazy.force coq_Z0 -> Bigint.zero
  | Term.App (f, [|a|]) when f = Lazy.force coq_Zpos -> tr_bigpositive a
  | Term.App (f, [|a|]) when f = Lazy.force coq_Zneg ->
      Bigint.neg (tr_bigpositive a)
  | Term.Cast (t, _, _) -> tr_arith_bigconstant t
  | _ -> raise (NotGappa t)

(** translate a closed Coq term [c:bool] into [bool] *)
let tr_bool c = match decompose_app c with
  | c, [] when c = Lazy.force coq_true -> true
  | c, [] when c = Lazy.force coq_false -> false
  | _ -> raise (NotGappa c)

let tr_float b m e =
  (b, tr_arith_bigconstant m, tr_arith_bigconstant e)

let tr_binop c = match decompose_app c with
  | c, [] when c = Lazy.force coq_boAdd -> Bplus
  | c, [] when c = Lazy.force coq_boSub -> Bminus
  | c, [] when c = Lazy.force coq_boMul -> Bmult
  | c, [] when c = Lazy.force coq_boDiv -> Bdiv
  | _ -> assert false

let tr_unop c = match decompose_app c with
  | c, [] when c = Lazy.force coq_uoNeg -> Uopp
  | c, [] when c = Lazy.force coq_uoSqrt -> Usqrt
  | c, [] when c = Lazy.force coq_uoAbs -> Uabs
  | _ -> raise (NotGappa c)

(** translate a Coq term [c:RExpr] into [term] *)
let rec tr_term uv t =
  match decompose_app t with
    | c, [a] when c = Lazy.force coq_reUnknown ->
        let n = tr_positive a - 1 in
        if (n < Array.length uv) then Tvar uv.(n)
        else raise (NotGappa t)
    | c, [a; b] when c = Lazy.force coq_reFloat2 ->
        Tconst (Constant.create (tr_float 2 a b))
    | c, [a; b] when c = Lazy.force coq_reFloat10 ->
        Tconst (Constant.create (tr_float 10 a b))
    | c, [a] when c = Lazy.force coq_reInteger ->
        Tconst (Constant.create (1, tr_arith_bigconstant a, Bigint.zero))
    | c, [op;a;b] when c = Lazy.force coq_reBinary ->
        Tbinop (tr_binop op, tr_term uv a, tr_term uv b)
    | c, [op;a] when c = Lazy.force coq_reUnary ->
        Tunop (tr_unop op, tr_term uv a)
    | c, [fmt;mode;a] when c = Lazy.force coq_reRound ->
        let mode = match decompose_app mode with
          | c, [] when c = Lazy.force coq_mRndDN -> "dn"
          | c, [] when c = Lazy.force coq_mRndNA -> "na"
          | c, [] when c = Lazy.force coq_mRndNE -> "ne"
          | c, [] when c = Lazy.force coq_mRndUP -> "up"
          | c, [] when c = Lazy.force coq_mRndZR -> "zr"
          | _ -> raise (NotGappa mode) in
        let rnd = match decompose_app fmt with
          | c, [e;p] when c = Lazy.force coq_fFloat ->
              let e = tr_arith_constant e in
              let p = tr_arith_constant p in
              sprintf "float<%d,%d,%s>" p e mode
          | c, [e] when c = Lazy.force coq_fFixed ->
              let e = tr_arith_constant e in
              sprintf "fixed<%d,%s>" e mode
          | _ -> raise (NotGappa fmt) in
        Tround (rnd, tr_term uv a)
    | _ ->
        raise (NotGappa t)

let tr_const c =
  match tr_term [||] c with
    | Tconst v -> v
    | _ -> raise (NotGappa c)

(** translate a Coq term [t:RAtom] into [pred] *)
let tr_atom uv t =
  match decompose_app t with
    | c, [l;e;u] when c = Lazy.force coq_raBound ->
        let l = match decompose_app l with
          | (_, [_;l]) -> Some (tr_const l)
          | (_, [_]) -> None
          | _ -> assert false in
        let u = match decompose_app u with
          | (_, [_;u]) -> Some (tr_const u)
          | (_, [_]) -> None
          | _ -> assert false in
        if l = None && u = None then raise (NotGappa t);
        Ain (tr_term uv e, l, u)
    | c, [er;ex;l;u] when c = Lazy.force coq_raRel ->
        Arel (tr_term uv er, tr_term uv ex, tr_const l, tr_const u)
    | c, [er;ex] when c = Lazy.force coq_raEq ->
        Aeq (tr_term uv er, tr_term uv ex)
    | _ ->
        raise (NotGappa t)

(** translate a Coq term [t:RTree] into [pred] *)
let rec tr_pred uv t =
  match decompose_app t with
    | c, [a] when c = Lazy.force coq_rtAtom ->
        Patom (tr_atom uv a)
    | c, [a] when c = Lazy.force coq_rtNot ->
        Pnot (tr_pred uv a)
    | c, [a;b] when c = Lazy.force coq_rtAnd ->
        Pand (tr_pred uv a, tr_pred uv b)
    | c, [a;b] when c = Lazy.force coq_rtOr ->
        Por (tr_pred uv a, tr_pred uv b)
    | _ ->
        raise (NotGappa t)

let tr_var c = match kind_of_term c with
  | Var x -> string_of_id x
  | _ -> raise (NotGappa c)

(** translate a Coq term [t:list] into [list] by applying [f] to each element *)
let tr_list f =
  let rec aux c =
    match decompose_app c with
      | _, [_;h;t] -> f h :: aux t
      | _, [_] -> []
      | _ -> raise (NotGappa c)
    in
  aux

(** translate a Coq term [c] of kind [convert_tree ...] *)
let tr_goal c =
  match decompose_app c with
    | c, [uv;e] when c = Lazy.force coq_convert_tree ->
        let uv = Array.of_list (tr_list tr_var uv) in
        tr_pred uv e
    | _ -> raise (NotGappa c)

(** print a Gappa term *)
let rec print_term fmt = function
  | Tconst c -> Constant.print fmt c
  | Tvar s -> pp_print_string fmt s
  | Tbinop (op, t1, t2) ->
      let op =
        match op with
          | Bplus -> "+" | Bminus -> "-" | Bmult -> "*" | Bdiv -> "/"
        in
      fprintf fmt "(%a %s %a)" print_term t1 op print_term t2
  | Tunop (Uabs, t) ->
      fprintf fmt "|%a|" print_term t
  | Tunop (Uopp | Usqrt as op, t) ->
      let s =
        match op with
          | Uopp -> "-" | Usqrt -> "sqrt" | _ -> assert false
        in
      fprintf fmt "(%s(%a))" s print_term t
  | Tround (m, t) ->
      fprintf fmt "(%s(%a))" m print_term t

(** print a Gappa predicate *)
let print_atom fmt = function
  | Ain (t, Some c1, Some c2) ->
      fprintf fmt "%a in [%a, %a]"
        print_term t Constant.print c1 Constant.print c2
  | Ain (t, Some c, None) ->
      fprintf fmt "%a >= %a" print_term t Constant.print c
  | Ain (t, None, Some c) ->
      fprintf fmt "%a <= %a" print_term t Constant.print c
  | Ain (_, None, None) -> assert false
  | Arel (t1, t2, c1, c2) ->
      fprintf fmt "%a -/ %a in [%a,%a]"
        print_term t1 print_term t2 Constant.print c1 Constant.print c2
  | Aeq (t1, t2) ->
      fprintf fmt "%a = %a" print_term t1 print_term t2

let rec print_pred fmt = function
  | Patom a -> print_atom fmt a
  | Pnot t -> fprintf fmt "not (%a)" print_pred t
  | Pand (t1, t2) -> fprintf fmt "(%a) /\\ (%a)" print_pred t1 print_pred t2
  | Por (t1, t2) -> fprintf fmt "(%a) \\/ (%a)" print_pred t1 print_pred t2

let temp_file f = if !debug then f else Filename.temp_file f ""
let remove_file f = if not !debug then try Sys.remove f with _ -> ()

exception GappaFailed of string

(** print a Gappa goal from [p] and call Gappa on it,
    build a Coq term by calling [c_of_s] *)
let call_gappa c_of_s p =
  let gappa_in = temp_file "gappa_inp" in
  let c = open_out gappa_in in
  let fmt = formatter_of_out_channel c in
  fprintf fmt "@[{ %a }@]@." print_pred p;
  close_out c;
  let gappa_out = temp_file "gappa_out" in
  let gappa_err = temp_file "gappa_err" in
  let cmd = sprintf "gappa -Bcoq-lambda %s > %s 2> %s" gappa_in gappa_out gappa_err in
  let out = Sys.command cmd in
  if out <> 0 then begin
    let c = open_in_bin gappa_err in
    let len = in_channel_length c in
    let buf = String.create len in
    ignore (input c buf 0 len);
    close_in c;
    raise (GappaFailed buf)
  end;
  remove_file gappa_in;
  remove_file gappa_err;
  let cin = open_in gappa_out in
  let constr = c_of_s (Stream.of_channel cin) in
  close_in cin;
  remove_file gappa_out;
  constr

(** execute [f] after disabling globalization *)
let no_glob f =
  let dg = Dumpglob.coqdoc_freeze () in
  Dumpglob.pause ();
  let res =
    try f () with e ->
      Dumpglob.continue ();
      Dumpglob.coqdoc_unfreeze dg;
      raise e
    in
  Dumpglob.continue ();
  Dumpglob.coqdoc_unfreeze dg;
  res

(** replace all evars of any type [ty] by [(refl_equal true : ty)] *)
let evars_to_vmcast sigma (emap, c) =
  let emap = nf_evar_map emap in
  let change_exist evar =
    let ty = Reductionops.nf_betaiota emap (Evd.existential_type emap evar) in
    mkCast (mkApp (Lazy.force coq_refl_equal,
      [| Lazy.force coq_bool; Lazy.force coq_true|]), VMcast, ty) in
  let rec replace c =
    match kind_of_term c with
      | Evar ev -> change_exist ev
      | _ -> map_constr replace c
    in
  replace c

let constr_of_stream gl s =
  no_glob (fun () -> Constrintern.interp_open_constr (project gl) (pf_env gl)
    (Pcoq.Gram.Entry.parse Pcoq.Constr.constr (Pcoq.Gram.parsable s)))

let var_name = function
  | Name id ->
      let s = string_of_id id in
      let s = String.sub s 1 (String.length s - 1) in
      mkVar (id_of_string s)
  | Anonymous ->
      assert false

(** apply to the proof term [c] all the needed variables from the context
    and as many metas as needed to match hypotheses *)
let build_proof_term c =
  let bl, _ = decompose_lam c in
  List.fold_right (fun (x,t) pf -> mkApp (pf, [| var_name x |])) bl c

(** the [gappa_internal] tactic *)
let gappa_internal gl =
  try
    let g = tr_goal (pf_concl gl) in
    let (emap, pf) = call_gappa (constr_of_stream gl) g in
    let pf = evars_to_vmcast (project gl) (emap, pf) in
    let pf = build_proof_term pf in
    Tacmach.refine_no_check pf gl
  with
    | NotGappa t ->
      errorlabstrm "gappa_internal"
        (Pp.str "translation to Gappa failed (not a reduced constant?): " ++ Printer.pr_constr t)
    | GappaFailed s ->
      errorlabstrm "gappa_internal"
        (Pp.str "execution of Gappa failed:" ++ Pp.fnl () ++ Pp.str s)

(** {1 Packaging for [gappa_prepare; gappa_internal]: the [gappa] tactic} *)
let gappa_prepare =
  let id = Ident (dummy_loc, id_of_string "gappa_prepare") in
  lazy (Tacinterp.interp (Tacexpr.TacArg (dummy_loc, Tacexpr.Reference id)))

let gappa gl =
  Coqlib.check_required_library ["Gappa"; "Gappa_tactic"];
  Tactics.tclABSTRACT None (Tacticals.tclTHEN (Lazy.force gappa_prepare) gappa_internal) gl

TACTIC EXTEND gappatac_gappa
| [ "gappa" ] -> [ gappa ]
END

TACTIC EXTEND gappatac_gappa_internal
| [ "gappa_internal" ] -> [ gappa_internal ]
END

TACTIC EXTEND gappatac_gappa_quote
| [ "gappa_quote" ] -> [ gappa_quote ]
END
