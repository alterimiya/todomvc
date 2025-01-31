sig Title {}

sig Todo {
    title: one Title,
   completed: one Bool
}

enum Bool { True, False }

sig AppState {
    todos: set Todo
}{
 #AppState = 1
}


-- ToDoを追加する操作
pred addTodo[s: AppState, sNext: AppState, t: Todo, newTitle: Title] {
 newTitle in Title        -- 空でない
    t not in s.todos  =>-- 追加前には存在しないToDo
    sNext.todos = s.todos + t  -- 新しいToDoを追加
    t.completed = False
}

-- ToDoの完了状態を切り替える操作
pred toggleComplete[s: AppState, sNext: AppState, t: Todo] {
    t in s.todos => -- 存在するToDo
   sNext.todos = (s.todos - t) + { t: Todo | 
    t.completed = True => t.completed = False else t.completed = True
}
}

-- 完了済みのToDoを削除する操作
pred clearCompleted[s: AppState, sNext: AppState] {
    sNext.todos = { t: s.todos | t.completed = False } -- 未完了のToDoのみ残す
}

assert addNewTodoSuccess{
	all s,sNext:AppState,t:Todo, T:Title|
		t not in s.todos  and T in Title implies addTodo[s,sNext,t,T] 
				    implies t in sNext.todos and t.completed = False
}

assert addOldTodoFail{
    all s,sNext:AppState,t:Todo, T:Title|
		t in s.todos or T not in Title implies addTodo[s,sNext,t,T] 
			     implies t in sNext.todos 
}

assert clearCompleted{
	 all s,sNext:AppState,t:Todo|
		t in s.todos and t.completed = True implies clearCompleted[s,sNext]
								 implies t not in sNext.todos 
}
assert noCompleted{
	 all s,sNext:AppState,t:Todo|
		t in s.todos and t.completed = False   implies not clearCompleted[s,sNext]
								implies t in sNext.todos
}

assert FTtoggleComplete{
	 all s,sNext:AppState,t:Todo|
		t in s.todos and t.completed = False   implies  toggleComplete[s,sNext,t]
								implies t in sNext.todos and t.completed = True
}

assert TFtoggleComplete{
 	all s,sNext:AppState,t:Todo|
		t in s.todos and t.completed = True   implies  toggleComplete[s,sNext,t]
								implies t in sNext.todos and t.completed = False
}

assert notoggleComplete{
	 all s,sNext:AppState,t:Todo|
		t not in s.todos implies not  toggleComplete[s,sNext,t]
								implies t not in sNext.todos 
}

//run addTodo  for 2 but 1 AppState
//run toggleComplete for 2  but 2 AppState
//check addNewTodoSuccess for 5
//check noCompleted
//check notoggleComplete
//check clearCompleted
//check addOldTodoFail
