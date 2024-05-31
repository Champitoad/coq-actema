open Utils.Pervasive
open Api
open Logic
open ProverLogic

module Pred = struct
  type t = Proof.t -> Logic.lemma -> bool

  let true_ _ _ = true
  let false_ _ _ = false
  let and_ p1 p2 proof lemma = p1 proof lemma && p2 proof lemma
  let or_ p1 p2 proof lemma = p1 proof lemma || p2 proof lemma
  let all ps proof lemma = List.for_all (fun p -> p proof lemma) ps
  let any ps proof lemma = List.exists (fun p -> p proof lemma) ps

  let match_name pattern _ lemma =
    (* Check that the pattern is an exact substring of the lemma's name.
       The test is case-insensitive. *)
    let user_name = String.lowercase_ascii @@ Name.show lemma.l_user in
    let pattern = String.lowercase_ascii pattern in
    try
      ignore (String.find user_name pattern);
      true
    with Not_found -> false

  (*let prepare_goal proof stmt selection : Proof.t * Path.t * Path.t =
      let Proof.{ g_id; g_pregoal = sub } = PathUtils.goal proof selection in
      (* Make a new goal that has :
         - the lemma as a local hypothesis.
         - its environment extended with the environment of the lemma database. *)
      let hd = Handle.fresh () in
      let sub =
        let hyp = Proof.mk_hyp stmt in
        let g_hyps = Proof.Hyps.add sub.g_hyps hd hyp in
        let g_env =
          Env.union (Proof.Lemmas.env @@ Proof.get_db proof) sub.g_env
        in
        Proof.{ sub with g_hyps; g_env }
      in
      (* Replace the current goal by the new goal. *)
      let g_ids, proof = Proof.Tactics.xprogress proof g_id [ sub ] in
      let g_id = List.hd g_ids in
      (* Create a path to the root of the new hypothesis (representing the lemma). *)
      let lemma_path =
        IPath.make
          ~ctxt:{ kind = `Hyp; handle = Handle.toint hd }
          (Handle.toint g_id)
      in
      (* Make sure the path to the selection is in the new goal. *)
      let selection =
        IPath.make ~ctxt:selection.ctxt ~sub:selection.sub (Handle.toint g_id)
      in
      (proof, lemma_path, selection)

    let subpath p sub = IPath.{ root = p.root; ctxt = p.ctxt; sub = p.sub @ sub }*)

  let link_sfl selection proof lemma = failwith "link_sfl: todo"
  (* Create a link predicate for subformula linking. *)
  (*let hlpred = Link.Pred.wf_subform in
    (* Prepare the goal. *)
    let proof, lemma_path, selection =
      prepare_goal proof lemma.Proof.l_form selection
    in
    (* Test against relevant links. As we are testing for subformula linking,
       we only select subpaths of the lemma that lead to a formula. *)
    List.exists
      begin
        fun sub ->
          not @@ List.is_empty
          @@ hlpred proof ([ subpath lemma_path sub ], [ selection ])
      end
      (f_subs lemma.Proof.l_form)*)

  (** Compute all the paths in a formula that lead to the left or right side of an equality. *)
  (*let eq_subs (f : form) : int list list =
    let rec aux (f : form) sub =
      match f with
      | FTrue | FFalse -> []
      | FBind (_, _, _, f) -> aux f (0 :: sub)
      | FConn (_, fs) ->
          fs |> List.mapi (fun i f -> aux f (i :: sub)) |> List.concat
      | FPred ("_EQ", [ e1; e2 ]) -> List.map List.rev [ 0 :: sub; 1 :: sub ]
      | FPred (_, _) -> []
    in
    aux f []*)

  let link_drewrite selection proof lemma = failwith "link_drewrite : todo"
  (*(* Create a link predicate for subformula linking. *)
    let hlpred = Link.Pred.deep_rewrite in
    (* Prepare the goal. *)
    let proof, lemma_path, selection =
      prepare_goal proof lemma.Proof.l_form selection
    in
    (* Test against relevant links.  As we are testing for deep rewrites,
       we only select subpaths of the lemma that lead to the left or right of an equality.
       This looses a bit of generality as we may miss some links that allow the selection to rewrite in the lemma. *)
    List.exists
      begin
        fun sub ->
          not @@ List.is_empty
          @@ hlpred proof ([ subpath lemma_path sub ], [ selection ])
      end
      (eq_subs lemma.Proof.l_form)*)
end

let filter pred proof = proof
(*let new_db = Proof.Lemmas.filter (pred proof) (Proof.get_db proof) in
  js_log
  @@ Format.sprintf "Filtered lemmas : %d\n"
       (List.length @@ Proof.Lemmas.ids new_db);
  Proof.set_db proof new_db*)
