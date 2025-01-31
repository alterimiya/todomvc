# Alloyによる形式検証の実習

## 検証対象のOSS

 TodoMVCは、さまざまなJavaScriptフレームワークやライブラリを用いたTodoアプリケーションの実装例を集めたプロジェクトである。実装例の中からJavaScript ES6に基づくものを選択した。Todoアプリケーションとしてはモジュール分割されたコード構造を持つシンプルなアプリケーションである。
 参考
 * TodoMVC公式ドキュメント: https://todomvc.com/
 * 検証対象のリポジトリ: https://github.com/tastejs/todomvc
 * 選択した実装のディレクトリ: https://github.com/tastejs/todomvc/tree/master/examples/javascript-es6

## 検証すべき性質

Todoの追加・削除・完了の性質について検証する。これらは、Todoリストとして最も基本的な性質の中の一つである。TodoMVCの仕様を参考として、検証する具体的な性質は以下のようである。
* Todoの追加：新しくTodoを追加する。このとき、タイトルの入力は空でなく、状態は未完了状態である。
* Todoの削除：完了状態のTodoを削除する。
* Todoの完了：Todoが未完了状態であれば完了状態にし、完了状態であれば未完了状態にする。

参考
* TodoMVCの仕様: https://github.com/tastejs/todomvc/blob/master/app-spec.md#functionality

## モデル化

作成したAlloyの記述は以下のようになった。
```alloy
sig Title {}

sig Todo {
    title: one Title,
   completed: one Bool
}

enum Bool { True, False }--True:完了 False:未完了

sig AppState {
    todos: set Todo
}{
    #AppState = 1
}


-- ToDoを追加する操作
pred addTodo[s: AppState, sNext: AppState, t: Todo, newTitle: Title] {
    newTitle in Title          -- 入力は空でない
    t not in s.todos  =>       -- 追加前には存在しないToDo
    sNext.todos = s.todos + t  -- 新しいToDoを追加
    t.completed = False
}

-- ToDoの完了状態を切り替える操作
pred toggleComplete[s: AppState, sNext: AppState, t: Todo] {
    t in s.todos =>            -- 存在するToDo
    sNext.todos = (s.todos - t) + { t: Todo | 
    t.completed = True => t.completed = False else t.completed = True           -- もとのtodoを引き切り替えたものを足す
}
}

-- 完了済みのToDoを削除する操作
pred clearCompleted[s: AppState, sNext: AppState] {
    sNext.todos = { t: s.todos | t.completed = False } -- 未完了のToDoのみ残す
}
```
Alloyの記述と元OSSの対応は以下のようになる。
#### モデル化とOSS実装の対応表

| Alloy モデル | OSS の実装 | 説明 |
|-------------|-----------|------|
| `sig AppState` | `class Model` | アプリの全体状態（ToDo リスト）を管理 |
| `sig Todo` | `newItem`（`create` 内） | ToDo アイテムの定義 |
| `pred addTodo` | `create(title, callback)` | ToDo の追加処理 |
| `pred clearCompleted` | `removeCompletedItems()` | 完了済みの ToDo を一括削除 |
| `pred toggleComplete` | `update(id, { completed }, callback)` | ToDo の完了状態の切り替え |





## 検証手法

* 設計したモデルの上で，どのような考えを持って検証したのか説明する．
* Alloyで記述した性質が，前掲の検証すべき性質に対応していることを具体的に説明する．
新しいTodoを追加する　assert
トグルで反転する
登録されているTodoを消す

各述語の操作を検証する。
* addTodo
  addTodoは「新たなTodoを追加する」操作を行う。また、このTodoのタイトルの入力は空でなく、状態は未完了である。よって検証内容は以下の通りである。
  * 「Todosに追加されていない新たなタイトルが空でないTodoを追加する」とき、AppStateは「変化あり」かつ「Todoが追加されている」。
  * 「既に追加されているまたはタイトルが空のTodoを追加する」とき、Appstateは「変化なし」
これらに基づいて記述したAlloyは以下のようである。
```alloy
assert addNewTodoSuccess{
	all s,sNext:AppState,t:Todo, T:Title|
		t not in s.todos and T in Title implies addTodo[s,sNext,t,T] 
				 implies t in sNext.todos and t.completed = False
}

assert addOldTodoFail{
    all s,sNext:AppState,t:Todo, T:Title|
		t in s.todos or T not in Title implies addTodo[s,sNext,t,T] 
			     implies t in sNext.todos 
}
```
これを`check addNewTodoSuccess for 5`、`check addOldTodoFail for 5`により実行したところ、反例は見つからず、妥当となった。よって、「Todoの追加：新しくTodoを追加する。このとき、タイトルの入力は空でなく、状態は未完了状態である。」性質が検証された。

* clearCompleted
clearCompletedは、「完了状態のToDoを一括削除」の操作を行う。検証内容は以下のとおりである。
  * 「Todosに追加されている完了状態であるTodoを削除する」とき、AppStateは「変化あり」かつ「Todoが削除されている」。
  * 「Todosに追加されているTodoが未完了状態である」とき、AppStateは「変化なし」。
これらに基づいて記述したAlloyは以下のようである。
```alloy
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
```
これを`check clearCompleted for 5`、`check noCompleted for 5`により実行したところ、反例は見つからず、妥当となった。よって、「Todoの削除：完了状態のTodoを削除する。」性質が検証された。
* toggleComplete
toggleCompleteは「Todoの完了状態の切り替え」の操作を行う。検証内容は以下のようである。
  * 「Todosに追加されている完了状態であるTodoの完了状態を切り替える」とき、AppStateは「変化あり」かつ「Todoが未完了状態である」。
  * 「Todosに追加されている完了状態であるTodoの完了状態を切り替える」とき、AppStateは「変化あり」かつ「Todoが未完了状態である」。
  * 「Todosに追加されていないTodoの完了状態を切り替える」とき、AppStateは「変化なし」。
これらに基づいて記述したAlloyは以下のようである。
```alloy
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
```
これを`check FTtoggleComplete for 5`、`check TFtoggleComplete for 5`、`check notoggleComplete for 5`により実行したところ、反例は見つからず、妥当となった。よって、「Todoの完了：Todoが未完了状態であれば完了状態にし、完了状態であれば未完了状態にする。」性質が検証された。
## 補足事項

リポジトリ内のファイル構造は以下のようである。
```
├── alloy-practice/
  │    ├── model.als
  │    ├── README.md       --本レポート
  │    ├── javascript-es6  --使用したOSS
```
