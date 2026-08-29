import SanguoshaNew.Examples

namespace SanguoshaNew

/-!
这份文件是给学员看的练习区。
目标不是继续堆新规则，而是把夏校里常见的证明动作单独拎出来：
`rfl`、`simp`、`decide`、`cases`、`omega`。
这样做的好处是，项目会更像一份可复用的课程笔记。
-/

/-- 练习 1：`PlayerId.next` 连做两次会回到原来的玩家。 -/
theorem playerId_next_involutive (p : PlayerId) :
    PlayerId.next (PlayerId.next p) = p := by
  cases p <;> rfl

/-- 练习 2：空牌池的总数就是 0。 -/
example : CardPool.total CardPool.empty = 0 := by
  rfl

/-- 练习 3：一旦满足“受伤”，`healOne` 就会把体力加 1。 -/
theorem healOne_hp_of_wounded (p : PlayerState) (h : p.wounded) :
    (p.healOne).hp = p.hp + 1 := by
  unfold PlayerState.wounded at h
  simp [PlayerState.healOne, h]

/-- 练习 4：自然数里，减去一个量以后不会超过原值。 -/
theorem nat_sub_le_self (n k : Nat) : n - k <= n := by
  omega

/-- 练习 5：在这个例子里，A 对 B 出杀是合法的。 -/
example : legal oneSlashState (Command.useSlash PlayerId.a PlayerId.b) := by
  decide

/-- 练习 6：同一个例子里，A 反过来对自己出杀是非法的。 -/
example : transition oneSlashState (Command.useSlash PlayerId.b PlayerId.a) = none := by
  decide

/-- 练习 7：合法命令会返回 `some`，而且结果正是对应的无检查执行。 -/
example :
    transition oneSlashState (Command.useSlash PlayerId.a PlayerId.b)
      = some (useSlashUnchecked oneSlashState PlayerId.a PlayerId.b) := by
  rfl

/-- 练习 8：`usePeachUnchecked` 的效果可以直接算出来。 -/
example :
    (usePeachUnchecked peachState PlayerId.a PlayerId.a).playerA.hp = 4 := by
  decide

/-- 练习 9：空牌池加一张牌以后，总数就是 1。 -/
example : (CardPool.empty.inc CardName.wine).total = 1 := by
  simp

/-- 练习 10：摸到一张牌，私人区总数会加 1。 -/
example :
    (peachState.playerA.gainToHand CardName.wine).cardTotal
      = peachState.playerA.cardTotal + 1 := by
  simp

/-- 练习 11：受到伤害不会改变私人区总牌数。 -/
example :
    (peachState.playerA.damage 2).cardTotal = peachState.playerA.cardTotal := by
  simp

/-- 练习 12：回 1 点体力也不会改变私人区总牌数。 -/
example :
    (peachState.playerA.healOne).cardTotal = peachState.playerA.cardTotal := by
  simp

end SanguoshaNew
