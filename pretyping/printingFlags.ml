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
(* XXX why does extern look at this flag? *)
let print_universes = make_flag ["Printing";"Universes"] false

(* detyping *)
let { Goptions.get = print_sort_quality } =
  Goptions.declare_bool_option_and_ref
    ~key:["Printing";"Sort";"Qualities"]
    ~value:true
    ()

(* detyping *)
let print_evar_arguments = make_flag ["Printing";"Existential";"Instances"] false

(* detyping *)
let { Goptions.get = print_wildcard } =
  Goptions.declare_bool_option_and_ref
    ~key:["Printing";"Wildcard"]
    ~value:true
    ()

(* detyping *)
let { Goptions.get = fast_name_generation } =
  Goptions.declare_bool_option_and_ref
    ~key:["Fast";"Name";"Printing"]
    ~value:false
    ()

(* detyping *)
let { Goptions.get = synthetize_type } =
  Goptions.declare_bool_option_and_ref
    ~key:["Printing";"Synth"]
    ~value:true
    ()

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

(* extern *)
let { Goptions.get = print_use_implicit_types } =
  Goptions.declare_bool_option_and_ref
    ~key:["Printing";"Use";"Implicit";"Types"]
    ~value:true
    ()

(* extern *)
let { Goptions.get = get_record_print } =
  Goptions.declare_bool_option_and_ref
    ~key:["Printing";"Records"]
    ~value:true
    ()
