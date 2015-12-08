Set Implicit Arguments.

Local Open Scope list_scope.

Fixpoint list_complete_for {A B P}
         (true : P)
         (false : P)
         (and : P -> P -> P)
         (args : list A) (values : list B)
         (is_good : A -> list A -> B -> P)
: P
  := match args, values with
       | nil, _ => true
       | _::_, nil => false
       | arg::args, v::vs =>
         and (is_good arg args v)
             (list_complete_for true false and args vs is_good)
     end.
