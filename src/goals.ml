open Goal
open Formula
open Id

type dgoals =
  | OnCurrent of dgoal
  | PushGoal of goal
  | PopGoal of goal
  | Identity
  | Compose of dgoals list

let push_goal goal = PushGoal goal
