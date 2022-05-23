(* Prop *)
let prop = EConstr.mkSort Sorts.prop

(* forall (A: Prop), A *)
let id =
  let name = Names.Name.mk_name (Names.Id.of_string "A") in
  let binder = Context.make_annot name Relevant in
  EConstr.mkProd (binder, prop, EConstr.mkRel 0)

(* State for an actema proof *)
module State = struct
  type t =
    { ps : Vernacstate.Parser.t
    ; pf : Declare.Proof.t
    }

  let make pf =
    { ps = Vernacstate.Parser.init ()
    ; pf = pf
    }
end

let new_proof typ : State.t =
  let evd = Evd.empty in
  let info = Declare.Info.make () in
  let name = Names.Id.of_string "thm_id" in
  let cinfo = Declare.CInfo.make ~name ~typ () in
  State.make (Declare.Proof.start ~info ~cinfo evd)

let id_proof () = new_proof id

let get_goals { State.pf; _ } =
  let pf = Declare.Proof.get pf in
  let { Proof.sigma; goals; _ } = Proof.data pf in
  List.map (fun it -> Printer.pr_goal {sigma; it}) goals

(* Returns None when EOF, otherwise throws! *)
let parse ps stm : _ option =
  let pa = Pcoq.Parsable.make (Stream.of_string stm) in
  let proof_mode = Pvernac.lookup_proof_mode "classic" in
  let entry = Pvernac.main_entry proof_mode in
  Vernacstate.Parser.parse ps entry pa

(* Not good *)
module Type_clas = struct
  type tac
  type term
end

type 'a obj =
  | Tac : unit Proofview.tactic -> Type_clas.tac obj

let interp (t : Vernacexpr.vernac_expr) : 'a obj = Obj.magic t

let interp_tactic t : unit Proofview.tactic option =
  Obj.magic t

let parse_tactic { State.ps; _ } tactic =
  (* XXX: Error handling of parsing *)
  let tac_ast = parse ps tactic in
  interp_tactic tac_ast

let refine_tactic = Obj.magic

let send_tactic { State.ps; pf } tac : State. t =
  let pf, _ = Declare.Proof.by tac pf in
  { ps; pf }

(* let goal : EConstr.t = Evar.concl g1 in
 * let hyps : NamedContext.t = Evar.evar_context g1 in *)

(*
Evd.evar_map
EConstr.t
Evar.t
NamedContext.t
Proof.t == evar_map



a      : T
a := t : T

"Plan"

- branch linking with Coq (build against Coq OPAM / all the good .vo files)
- initialize Coq from actema
- Build Example proof such, p = "forall (A : Prop) -> A"
- let pf = Declare.Proof.start p in

- a. display in actema Coq's proof state
- b. send some tactics or refine
- c. if not end goto a.

- Declare.Proof.save pf        "QED"



*)
