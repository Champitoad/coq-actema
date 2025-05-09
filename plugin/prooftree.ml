open Utils.Pervasive
open Api

(* the type for prooftrees *)
(* 'a for actions, 'g for goals *)
type tree =
    Tree of Logic.goal option * ( goal_state) ref
and (* and list of mutable subgoals *)
    goal_state =
  | Open
  | Node of Logic.action * ((tree) list);;

(* the goals list points to the leafs in the tree *)
type proofTree =
  {tree : tree;
   mutable goals : (( tree) list);
   mutable history :  (((tree) *  (( tree) list)) list) };;


let newtree g =
  let r : goal_state ref = ref Open in
  Tree (g, r);;

let newProofTree g =
  let t = newtree g in
  {tree = t; goals = [t]; history = [] };;

let get_goal t n =
  match (List.nth t.goals n) with
    Tree(g,_) -> g;;

let goal_to_tree =
  List.map (fun g -> Tree (g, ref Open));; 

let update_goal_t (Tree(g,s)) a l =
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

let perform n a l t = 
  let l = goal_to_tree l in
  let (l1, l2, g) = split t.goals n in
  update_goal_t g a l;
  t.history <- (g, t.goals)::t.history;
  t.goals <- l1@l@l2;;

let undo_t t =
  match t.history with
  | [] -> failwith "undo"
  | (Tree(g, st), gl)::l ->
    st := Open;
    t.goals <- gl;
    t.history <- l;;
 

let rec size (Tree (_, r)) =
   match !r with
  | Open -> 0
  | Node (a,l) ->
    1 + (List.fold_left (fun n a -> n + (size a)) 0 l);;
  
