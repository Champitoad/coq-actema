open Utils.Pervasive
open Api
    
(* the type for prooftrees *)
(* 'a for actions, 'g for goals *)
type tree =
    Tree of Logic.goal * goal_state ref
and (* and list of mutable subgoals *)
    goal_state =
  | Open
  | Node of Logic.action * (tree list);;

(* the goals list points to the leafs in the tree *)
type proofTree =
  {tree : tree;
   mutable goals : (Logic.goal * goal_state ref) list;
   mutable history :  (goal_state ref * ((Logic.goal * (goal_state ref) ) list)) list };;


let newtree c =
  let r : goal_state ref = ref Open in
  (Tree (c, r), r);;

let newProofTree c =
  let t,r = newtree c in
  {tree = t; goals = [c,r]; history = [] };;

let get_subgoal t n =
  match (List.nth t.goals n) with
    (g,_) -> g;;

let term_to_subgoal =
  List.map (fun p -> Tree (p, ref Open));; 

let update_goal_t s a l =
  match !s with
  | Node _ -> failwith "update"
  | Open ->
      s := Node (a, l);;

let split l n =
  let rec aux n acc = function
    | [] -> failwith "split"
    | a::l ->
      if n = 0
      then (List.rev acc, l,a)
      else aux (n-1) (a::acc) l
  in aux n [] l;;

let rec get_subgoals = function
  | Tree (p, r) ->
    match !r with
    | Open -> [p,r]
    | Node (_,l) -> get_subgoals_aux l
and get_subgoals_aux = function
  | [] -> []
  | t::l -> (get_subgoals t)@(get_subgoals_aux l)

let perform n a l t = 
  let l = term_to_subgoal l in
  let (l1, l2, (g,r)) = split t.goals n in
  update_goal_t r a l;
  t.history <- (r, t.goals)::t.history;
  t.goals <- get_subgoals t.tree

let undo_t t =
  match t.history with
  | [] -> failwith "undo"
  | (r, _)::l ->
    r := Open;
    t.goals <- get_subgoals t.tree;
    t.history <- l;;
 

let rec size (Tree (_, r)) =
   match !r with
  | Open -> 0
  | Node (a,l) ->
    1 + (List.fold_left (fun n a -> n + (size a)) 0 l);;


let  action_to_string a = Logic.show_action a
let  term_to_string t = Lang.Term.show t

(*
type pregoal =
  { g_env : Env.t; g_vars : Vars.t; g_hyps : Hyps.t; g_concl : Term.t }
*)


let  pregoal_to_string (g : Logic.pregoal) = Lang.Term.show g.g_concl
let  goal_to_string (g : Logic.goal) = Lang.Term.show g.g_pregoal.g_concl



  
