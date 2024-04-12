open Fo
open CoreLogic
open Utils

let filter_by_name pattern proof =
  let db = proof |> Proof.get_db in
  let new_map =
    db.db_map
    |> Map.filter
         begin
           fun name _stmt ->
             (* Check that the pattern is an exact substring of the lemma's name.
                The test is case-insensitive. *)
             let name = String.lowercase_ascii name in
             let pattern = String.lowercase_ascii pattern in
             try
               ignore (String.find name pattern);
               true
             with Not_found -> false
         end
  in
  Proof.set_db proof { db with db_map = new_map }

let filter_by_selection selection proof =
  let open Link in
  (* Construct a hyperlink predicate to allow only valid linkactions. *)
  let filter =
    Pred.add
      [ Pred.mult (List.map Pred.lift [ Pred.wf_subform; Pred.intuitionistic ])
      ; Pred.lift @@ Pred.wf_subform ~drewrite:true
      ]
  in
  (* Filter the lemma database. *)
  let db = proof |> Proof.get_db in
  let new_map =
    db.db_map 
    |> Map.filter
         begin
           fun _name stmt ->
             (* Make a new goal that has :
                - the lemma as a local hypothesis.
                - its environment extended with the environment of the lemma database. *)
             let Proof.{ g_id; g_pregoal = sub } = IPath.goal proof selection in
             let hd = Handle.fresh () in
             let sub =
               let hyp = Proof.mk_hyp stmt in
               let g_hyps = Proof.Hyps.add sub.g_hyps hd hyp in
               let g_env = Env.union db.db_env sub.g_env in
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
             let selection =
               IPath.make ~ctxt:selection.ctxt ~sub:selection.sub (Handle.toint g_id)
             in
             (* Compute all linkactions. *)
             let linkactions =
               (* Here the source of the linkaction is fixed to the selection (no subterms),
                  but the destination is not fixed (we consider all subterms of the lemma). *)
               Pred.search_linkactions filter proof ~fixed_srcs:[ selection ]
                 (IPath.make (Handle.toint g_id), lemma_path)
             in
             not @@ List.is_empty linkactions
         end
    (* Note that the proof is modified in the predicate of LemmaDB.filter (we add a new hypothesis),
       but since it is an immutable structure the changes are not reflected here. *)
  in
  Proof.set_db proof { db with db_map = new_map }
