open Fo
open CoreLogic
open Utils

module Pred = struct
  type t = Proof.proof -> string -> string * form -> bool

  let true_ _ _ _ = true
  let false_ _ _ _ = false

  let and_ p1 p2 proof full_name (user_name, stmt) =
    p1 proof full_name (user_name, stmt) && p2 proof full_name (user_name, stmt)

  let or_ p1 p2 proof full_name (user_name, stmt) =
    p1 proof full_name (user_name, stmt) || p2 proof full_name (user_name, stmt)

  let all ps proof full_name (user_name, stmt) =
    List.for_all (fun p -> p proof full_name (user_name, stmt)) ps

  let any ps proof full_name (user_name, stmt) =
    List.exists (fun p -> p proof full_name (user_name, stmt)) ps

  let match_name pattern _ _ (user_name, _) =
    (* Check that the pattern is an exact substring of the lemma's name.
       The test is case-insensitive. *)
    let user_name = String.lowercase_ascii user_name in
    let pattern = String.lowercase_ascii pattern in
    try
      ignore (String.find user_name pattern);
      true
    with Not_found -> false

  let prepare_goal proof stmt selection : Proof.proof * IPath.t * IPath.t =
    let Proof.{ g_id; g_pregoal = sub } = IPath.goal proof selection in
    (* Make a new goal that has :
       - the lemma as a local hypothesis.
       - its environment extended with the environment of the lemma database. *)
    let hd = Handle.fresh () in
    let sub =
      let hyp = Proof.mk_hyp stmt in
      let g_hyps = Proof.Hyps.add sub.g_hyps hd hyp in
      let g_env = Env.union (Proof.get_db proof).db_env sub.g_env in
      Proof.{ sub with g_hyps; g_env }
    in
    (* Replace the current goal by the new goal. *)
    let g_ids, proof = Proof.Tactics.xprogress proof g_id [ sub ] in
    let g_id = List.hd g_ids in
    (* Create a path to the root of the new hypothesis (representing the lemma). *)
    let lemma_path =
      IPath.make ~ctxt:{ kind = `Hyp; handle = Handle.toint hd } (Handle.toint g_id)
    in
    (* Make sure the path to the selection is in the new goal. *)
    let selection = IPath.make ~ctxt:selection.ctxt ~sub:selection.sub (Handle.toint g_id) in
    (proof, lemma_path, selection)

  let subpath p sub = IPath.{ root = p.root; ctxt = p.ctxt; sub = p.sub @ sub }

  let link_sfl selection proof _ (_, stmt) =
    (* Create a link predicate for subformula linking. *)
    let hlpred =
      let open Link in
      Pred.mult @@ List.map Pred.lift [ Pred.wf_subform ~drewrite:false; Pred.intuitionistic ]
    in
    (* Prepare the goal. *)
    let proof, lemma_path, selection = prepare_goal proof stmt selection in
    (* Test against relevant links. As we are testing for subformula linking,
       we only select subpaths of the lemma that lead to a formula. *)
    List.exists
      begin
        fun sub -> not @@ List.is_empty @@ hlpred proof ([ subpath lemma_path sub ], [ selection ])
      end
      (f_subs stmt)

  (** Compute all the paths in a formula that lead to the left or right side of an equality. *)
  let eq_subs (f : form) : int list list =
    let rec aux (f : form) sub =
      match f with
      | FTrue | FFalse -> []
      | FBind (_, _, _, f) -> aux f (0 :: sub)
      | FConn (_, fs) -> fs |> List.mapi (fun i f -> aux f (i :: sub)) |> List.concat
      | FPred ("_EQ", [ e1; e2 ]) -> List.map List.rev [ 0 :: sub; 1 :: sub ]
      | FPred (_, _) -> []
    in
    aux f []

  let link_drewrite selection proof _ (_, stmt) =
    (* Create a link predicate for subformula linking. *)
    let hlpred =
      let open Link in
      Pred.lift @@ Pred.wf_subform ~drewrite:true
    in
    (* Prepare the goal. *)
    let proof, lemma_path, selection = prepare_goal proof stmt selection in
    (* Test against relevant links. *)
    List.exists
      begin
        fun sub -> not @@ List.is_empty @@ hlpred proof ([ subpath lemma_path sub ], [ selection ])
      end
      (eq_subs stmt)
end

let filter pred proof =
  let db = Proof.get_db proof in
  let new_map = Map.filter (pred proof) db.db_map in
  js_log @@ Format.sprintf "Filtered lemmas : %d\n" (Map.cardinal new_map);
  Proof.set_db proof { db with db_map = new_map }
