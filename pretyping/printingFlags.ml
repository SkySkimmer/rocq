(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

let make_flag key v =
  let r = ref v in
  let () =
    Goptions.declare_bool_option {
      optstage = Summary.Stage.Interp;
      optdepr  = None;
      optkey   = key;
      optread  = (fun () -> !r);
      optwrite = (fun b -> r := b);
    }
  in
  r

(* detyping + extern + random stuff *)
let raw_print = make_flag ["Printing";"All"] false

(* detyping + extern + a few extra things (eg About) *)
let print_universes = make_flag ["Printing";"Universes"] false

(* extern *)
let print_coercions = make_flag ["Printing";"Coercions"] false

(* extern + ppconstr *)
let print_parentheses = make_flag ["Printing";"Parentheses"] false

(* constant for now, TODO expose as a new option *)
(* extern *)
let print_implicits_explicit_args () = false

(* extern *)
let print_implicits = make_flag ["Printing";"Implicit"] false

(* extern *)
let print_implicits_defensive = make_flag ["Printing";"Implicit";"Defensive"] true

(* extern *)
let print_projections = make_flag ["Printing";"Projections"] false

(* extern *)
let print_no_symbol = ref false

let () =
  (* Printing Notations uses a negated ref for convenience in Himsg.explicit_flags *)
  Goptions.declare_bool_option
    { optstage = Summary.Stage.Interp;
      optdepr  = None;
      optkey   = ["Printing";"Notations"];
      optread  = (fun () -> not !print_no_symbol);
      optwrite = (fun b ->  print_no_symbol := not b);
    }

(* extern *)
let print_raw_literal = make_flag ["Printing";"Raw";"Literals"] false
