open Utils.Pervasive
open Proofview
open CoqUtils
open Api
open Translate

(* -------------------------------------------------------------------- *)
(** The actema tactic *)

type proof = (int * Logic.action) list

(** Export each coq goal to Actema. *)
let export_goals () : (Logic.goal list * SymbolTable.t) tactic =
  let open PVMonad in
  let* coq_goals = Goal.goals in
  let+ pregoals, tables = List.split <$> mapM (map Export.goal) coq_goals in
  let goals =
    List.mapi (fun i pgoal -> Logic.{ g_id = i; g_pregoal = pgoal }) pregoals
  in
  let table = List.fold SymbolTable.union SymbolTable.empty tables in
  (goals, table)

let export_lemmas () : (Logic.lemma list * Lang.Env.t * SymbolTable.t) tactic =
  let open PVMonad in
  let* coq_goals = Goal.goals in
  let+ lemmas, envs, tables =
    List.split3 <$> mapM (map Export.lemmas) coq_goals
  in
  let lemmas = List.concat lemmas in
  let env = List.fold Lang.Env.union Lang.Env.empty envs in
  let table = List.fold SymbolTable.union SymbolTable.empty tables in
  (lemmas, env, table)

let get_user_action (goals : Logic.goal list) : Client.action =
  if goals = []
  then begin
    Lwt_main.run (Client.send_qed ());
    Client.Done
  end
  else Lwt_main.run (Client.send_goals goals)

type history = { mutable before : proof; mutable after : proof }

exception ApplyUndo

(** The control flow here is a mess. *)
let interactive_proof () : proof tactic =
  let open PVMonad in
  (* The proof history used to manage Undo/Redo. *)
  let hist = ref { before = []; after = [] } in

  (* At the start of the proof translate the lemmas to the Actema format. *)
  let start = Sys.time () in
  let* lemmas, lemmas_env, lemmas_table = export_lemmas () in
  let stop = Sys.time () in
  Log.printf "Exported %d lemmas in %.2fs" (List.length lemmas) (stop -. start);

  (* This is the main loop of the plugin, where we handle all actions
     given by the frontend. *)
  let rec aux () =
    let open Client in
    (* Handle Undo/Redo. *)
    let continue idx a =
      let cont =
        let* _ = Actions.execute (idx, a) in
        aux ()
      in
      tclOR cont
        begin
          fun ((exn, _) as iexn) ->
            match exn with
            | ApplyUndo -> aux ()
            | _ ->
                let msg =
                  CErrors.iprint_no_report iexn |> Pp.string_of_ppcmds
                in
                Lwt_main.run (Client.send_error msg);
                !hist.before <- Stdlib.List.tl !hist.before;
                aux ()
        end
    in

    (* Get the next action that is NOT a lemma request. *)
    let rec handle_lemmas (act : action) : action =
      match act with
      (* We received a lemma request : send the lemmas and get the next action again. *)
      | Lemmas ->
          (* Send the lemmas to the server. *)
          let act = Lwt_main.run @@ Client.send_lemmas lemmas lemmas_env in
          (* Handle the next action. *)
          handle_lemmas act
      (* Otherwise we are done here. *)
      | _ -> act
    in

    (* Export the goals and get the next action. *)
    let* goals, _ = export_goals () in
    let act = handle_lemmas (get_user_action goals) in
    (* Handle the action. *)
    begin
      match act with
      | Lemmas ->
          Log.error
            "Actema_main.interactive_proof: call handle_lemmas on the action."
      | Do (idx, a) ->
          Log.printf "Received action %d :: %s" idx (Logic.show_action a);
          !hist.before <- (idx, a) :: !hist.before;
          continue idx a
      | Done -> return @@ List.rev !hist.before
      | Undo -> begin
          match !hist.before with
          | a :: before ->
              !hist.before <- before;
              !hist.after <- a :: !hist.after;
              tclZERO ApplyUndo
          | [] -> aux ()
        end
      | Redo -> begin
          match !hist.after with
          | (idx, a) :: after ->
              !hist.after <- after;
              !hist.before <- (idx, a) :: !hist.before;
              continue idx a
          | [] -> aux ()
        end
    end
  in

  aux ()

let actema_tac ?(force = false) (action_name : string) : unit tactic =
  let open PVMonad in
  Goal.enter
    begin
      fun coq_goal ->
        let goal, _ = Export.goal coq_goal in
        let id = (action_name, Logic.Hyps.to_list goal.g_hyps, goal.g_concl) in
        let interactive () =
          let* prf = interactive_proof () in
          Storage.save_proof id prf;
          return ()
        in
        if force
        then interactive ()
        else
          match Storage.load_proof id with
          | Some prf -> mapM_ Actions.execute prf
          | _ -> interactive ()
    end

(***************************************************************************************)

(*module ProverLogic = struct
    [@@@landmark "auto"]

    open Utils.Pervasive
    open Api
    open Lang
    open Logic

    module IntNameMap = Map.Make (struct
      type t = int * Name.t

      let compare = Stdlib.compare
    end)

    module Proof = struct
      type mkey = MGoal of int

      module MKeyMap = Map.Make (struct
        type t = mkey

        let compare = compare
      end)

      type mdata = unit

      type t =
        { p_goals : goal IntMap.t
              (** A map from goal handles to goals.
                Contains only the opened (i.e. currently active) goals. *)
        ; p_meta : mdata MKeyMap.t ref  (** Metadata. *)
        ; p_db : Lemmas.t  (** The lemma database. *)
        }

      let init goals =
        (* Type-check the goals, just to make sure. *)
        List.iter
          begin
            fun { g_id; g_pregoal } ->
              let check f =
                ignore (TermUtils.check g_pregoal.g_env Context.empty f)
              in
              check g_pregoal.g_concl;
              Hyps.iter
                (fun { h_name; h_gen; h_form } -> check h_form)
                g_pregoal.g_hyps
          end
          goals;
        (* Create the map from goal handles to goals. *)
        let p_goals =
          List.fold_left
            (fun p_goals g ->
              assert (not @@ IntMap.mem g.g_id p_goals);
              IntMap.add g.g_id g p_goals)
            IntMap.empty goals
        in
        { p_goals; p_meta = ref MKeyMap.empty; p_db = Lemmas.empty }

      let get_db (proof : t) = proof.p_db
      let set_db (proof : t) (db : Lemmas.t) = { proof with p_db = db }

      let set_meta proof key meta : unit =
        match meta with
        | None -> proof.p_meta := MKeyMap.remove key !(proof.p_meta)
        | Some meta -> proof.p_meta := MKeyMap.add key meta !(proof.p_meta)

      let get_meta proof key : mdata option = MKeyMap.find_opt key !(proof.p_meta)
      let is_closed (proof : t) = IntMap.is_empty proof.p_goals
      let opened (proof : t) = IntMap.keys proof.p_goals |> List.of_enum

      let byid (proof : t) (goal_id : int) : pregoal =
        let goal =
          Option.get_exn
            (IntMap.find_opt goal_id proof.p_goals)
            (InvalidGoalId goal_id)
        in
        goal.g_pregoal

      let xprogress (proof : t) (goal_id : int) (pregoals : pregoal list) =
        (* Get the maximum goal index currently in use. *)
        let max_id = proof.p_goals |> IntMap.keys |> List.of_enum |> List.max in
        (* Choose a goal id for each pregoal. *)
        let subgoals =
          let for1 i subgoal =
            let hyps = Hyps.bump subgoal.g_hyps in
            let sub = { subgoal with g_hyps = hyps } in
            { g_id = max_id + i + 1; g_pregoal = sub }
          in
          List.mapi for1 pregoals
        in
        let new_ids = List.map (fun x -> x.g_id) subgoals in

        (* The new subgoals get the same metadata as the old goal. *)
        let p_meta =
          match get_meta proof (MGoal goal_id) with
          | None -> !(proof.p_meta)
          | Some meta ->
              List.fold_left
                (fun map id -> MKeyMap.add (MGoal id) meta map)
                !(proof.p_meta) new_ids
        in

        (* Remove the old goal and add the new goals. *)
        let p_goals =
          proof.p_goals |> IntMap.remove goal_id
          |> List.fold_right
               (fun subgoal map -> IntMap.add subgoal.g_id subgoal map)
               subgoals
        in
        (* Don't forget to return the indices of the new goals. *)
        (new_ids, { proof with p_goals; p_meta = ref p_meta })

      let move proof ~goal_id ~hyp_name ~dest_name =
        let goal = byid proof goal_id in
        let hyps = Hyps.move goal.g_hyps hyp_name dest_name in

        snd @@ xprogress proof goal_id [ { goal with g_hyps = hyps } ]
    end

    module PathUtils = struct
      let goal (path : Path.t) proof : goal =
        try { g_id = path.goal; g_pregoal = Proof.byid proof path.goal }
        with InvalidGoalId _ -> raise @@ Path.InvalidPath (Path.to_string path)

      (** This is fast. *)
      let destr_aux (path : Path.t) proof : goal * item * Term.t =
        let goal = goal path proof in
        let pregoal = goal.g_pregoal in
        let exn = Path.InvalidPath (Path.to_string path) in
        match path.kind with
        | Path.Concl -> (goal, Concl pregoal.g_concl, pregoal.g_concl)
        | Path.Hyp hname ->
            let hyp =
              try Hyps.by_name pregoal.g_hyps hname
              with InvalidHyphName _ -> raise exn
            in
            (goal, Hyp (hname, hyp), hyp.h_form)
        | Path.VarHead vname ->
            let var =
              try Vars.by_name pregoal.g_vars vname
              with InvalidVarName _ -> raise exn
            in
            (goal, Var (vname, var.v_type, var.v_body), Term.mkCst vname)
        | Path.VarType vname ->
            let var =
              try Vars.by_name pregoal.g_vars vname
              with InvalidVarName _ -> raise exn
            in
            (goal, Var (vname, var.v_type, var.v_body), var.v_type)
        | Path.VarBody vname ->
            let var =
              try Vars.by_name pregoal.g_vars vname
              with InvalidVarName _ -> raise exn
            in
            let body = Option.get_exn var.v_body exn in
            (goal, Var (vname, var.v_type, var.v_body), body)

      (** This can take some time if [path.sub] is long. *)
      let destr path proof : goal * item * Context.t * Term.t =
        let goal, item, i_term = destr_aux path proof in
        let ctx, term =
          try TermUtils.subterm i_term path.sub
          with InvalidSubtermPath _ ->
            raise @@ Path.InvalidPath (Path.to_string path)
        in
        (goal, item, ctx, term)

      let item path proof : item =
        let _, item, _ = destr_aux path proof in
        item

      let term path proof : Term.t =
        let _, _, term = destr_aux path proof in
        term

      let ctx path proof : Context.t =
        let _, _, ctx, _ = destr path proof in
        ctx
    end
  end

  module LemmaUtils = struct
    [@@@landmark "auto"]

    open Utils.Pervasive
    open Api
    open Lang
    open Logic
    open ProverLogic

    (** Compute all the paths in a formula that lead to a subformula in the first order skeleton. *)
    let f_subs _env _context f : int list list =
      let rec loop f sub acc =
        let fo = FirstOrder.view _env _context f in
        match fo with
        | FAtom _ -> sub :: acc
        | FConn (conn, args) ->
            List.fold_lefti
              (fun acc i arg -> loop arg ((i + 1) :: sub) acc)
              (sub :: acc) args
        | FImpl (f0, f1) ->
            let acc = sub :: acc in
            let acc = loop f0 (0 :: sub) acc in
            loop f1 (1 :: sub) acc
        | FBind (Forall, x, ty, body) ->
            let acc = sub :: acc in
            let acc = loop ty (0 :: sub) acc in
            loop body (1 :: sub) acc
        | FBind (Exist, x, ty, body) ->
            let acc = sub :: acc in
            let acc = loop ty (1 :: sub) acc in
            loop body (1 :: 2 :: sub) acc
      in
      List.map List.rev @@ loop f [] []

    (** Compute all the paths in a formula that lead to the left or right side of an equality
      which is in the first-order skeleton. *)
    let eq_subs env context f : int list list =
      let rec loop context f sub acc =
        let fo = FirstOrder.view env context f in
        match fo with
        | FAtom (App (_, Cst eq, [ ty; t1; t2 ])) when Name.equal eq Constants.eq
          ->
            (2 :: sub) :: (3 :: sub) :: acc
        | FAtom _ -> acc
        | FConn (conn, args) ->
            List.fold_lefti
              (fun acc i arg -> loop context arg ((i + 1) :: sub) acc)
              acc args
        | FImpl (f0, f1) ->
            let acc = loop context f0 (0 :: sub) acc in
            loop context f1 (1 :: sub) acc
        | FBind (Forall, x, ty, body) ->
            let fvar, new_context = Context.add_fresh x ty context in
            let acc = loop context ty (0 :: sub) acc in
            loop new_context (Term.instantiate fvar body) (1 :: sub) acc
        | FBind (Exist, x, ty, body) ->
            let fvar, new_context = Context.add_fresh x ty context in
            let acc = loop context ty (1 :: sub) acc in
            loop new_context (Term.instantiate fvar body) (1 :: 2 :: sub) acc
      in
      List.map List.rev @@ loop context f [] []

    module Pred = struct
      let prepare_goal proof lemma selection : Proof.t * Path.t * Path.t =
        let { g_id; g_pregoal = pregoal } = PathUtils.goal selection proof in
        (* Make a new (pre)goal that has :
           - the lemma as a local hypothesis.
           - its environment extended with the environment of the lemma database. *)
        let new_pregoal =
          let g_hyps =
            Hyps.add pregoal.g_hyps
              { h_name = lemma.l_full; h_form = lemma.l_form; h_gen = 0 }
          in
          let g_env =
            (*Env.union (Lemmas.env @@ Proof.get_db proof) pregoal.g_env*)
            Lemmas.env @@ Proof.get_db proof
          in
          { pregoal with g_hyps; g_env }
        in
        (* Replace the current goal by the new goal. *)
        let new_g_ids, proof = Proof.xprogress proof g_id [ new_pregoal ] in
        let new_g_id = List.hd new_g_ids in
        (* Create a path to the root of the new hypothesis (representing the lemma). *)
        let lemma_path = Path.make ~kind:(Hyp lemma.l_full) new_g_id in
        (* Make sure the path to the selection is in the new goal. *)
        let selection = { selection with goal = new_g_id } in
        (proof, lemma_path, selection)

      let subpath p sub = Path.{ p with sub = p.sub @ sub }

      let link_sfl selection proof lemma =
        (* Create a link predicate for subformula linking. *)
        let hlpred _ _ = [] in
        (* Prepare the goal. *)
        let proof, lemma_path, selection = prepare_goal proof lemma selection in
        let goal = Proof.byid proof lemma_path.goal in
        (* Test against relevant links. As we are testing for subformula linking,
           we only select subpaths of the lemma that lead to a formula. *)
        let subs = f_subs goal.g_env Context.empty lemma.l_form in
        let res =
          List.exists
            begin
              fun sub ->
                not @@ List.is_empty
                @@ hlpred proof ([ subpath lemma_path sub ], [ selection ])
            end
            subs
        in
        res
    end

    let[@landmark] filter pred proof =
      let old_db = Proof.get_db proof in
      let[@landmark] new_db = Lemmas.filter (pred proof) old_db in
      Proof.set_db proof new_db
  end*)

(*let test_filter () =
    let open PVMonad in
    let open Logic in
    let open ProverLogic in
    let* goals = export_goals () in
    let* lemmas, env = export_lemmas () in
    let db = Lemmas.of_list lemmas |> Lemmas.extend_env env in
    let proof = Proof.init goals |> Fun.flip Proof.set_db db in
    (* Actual computation. *)
    let selection = Path.make 0 in
    let[@landmark "filter-sfl"] _ =
      LemmaUtils.filter (LemmaUtils.Pred.link_sfl selection) proof
    in
    Tacticals.tclIDTAC

  let test_tac () : unit tactic =
    Landmark.start_profiling ();

    PVMonad.bind (test_filter ()) @@ fun _ ->
    let graph = Landmark.export () in
    Out_channel.with_open_text
      "/home/mathis/Documents/work/coq-actema/landmark-graph.json"
    @@ fun file ->
    Landmark.Graph.output_json file graph;
    Landmark.stop_profiling ();

    Tacticals.tclIDTAC
*)

let test_tac () : unit tactic = Tacticals.tclIDTAC
