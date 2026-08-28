import SanguoshaNew.Invariant

namespace SanguoshaNew

/-
这个文件放可以直接读懂的小例子。

Lean 里的 `example` 和 `theorem` 很像，只是不起名字。
它适合用来写“这个局面下，这个规则应该得到什么结果”。

如果以后改规则导致某个 `example` 编译失败，说明新规则和旧预期冲突了。
-/

/--
例 1：A 在出牌阶段，手里有一张【杀】；B 只有 1 点体力。

这个局面用来演示：
* A 对 B 使用【杀】是合法的；
* 如果 B 不出【闪】，结算后 B 的体力变为 0。
-/
def oneSlashState : GameState :=
  { current := PlayerId.a
    phase := Phase.play
    timing := Timing.idle
    playerA := { hp := 4, maxHp := 4, hand := { CardPool.empty with slash := 1 } }
    playerB := { hp := 1, maxHp := 4, hand := CardPool.empty } }

/-- Lean 可以自动判断：在 `oneSlashState` 中，A 对 B 出【杀】合法。 -/
example : legal oneSlashState (Command.useSlash PlayerId.a PlayerId.b) := by
  decide

/--
`transition` 返回 `some ...`，说明行动合法并成功产生新局面。

这里的 `rfl` 表示左右两边按定义展开后完全一样。
-/
example :
    transition oneSlashState (Command.useSlash PlayerId.a PlayerId.b)
      = some (useSlashUnchecked oneSlashState PlayerId.a PlayerId.b) := by
  rfl

/-- B 没有出【闪】时，结算这张【杀】后 B 的体力是 0。 -/
example :
    let afterSlash := useSlashUnchecked oneSlashState PlayerId.a PlayerId.b
    (settleSlashUnchecked afterSlash).playerB.hp = 0 := by
  decide

/--
例 2：B 正在响应 A 的【杀】，并且 B 手牌里有一张【闪】。

`processing` 里的一张【杀】表示这张杀已经被使用，但还没有完全结算。
`pendingSlash` 记录这张杀的来源、目标和伤害。
-/
def dodgeState : GameState :=
  { current := PlayerId.a
    phase := Phase.play
    timing := Timing.response
    playerA := { hp := 4, maxHp := 4, hand := CardPool.empty }
    playerB := { hp := 4, maxHp := 4, hand := { CardPool.empty with dodge := 1 } }
    processing := { CardPool.empty with slash := 1 }
    pendingSlash := some { source := PlayerId.a, target := PlayerId.b, damage := 1 } }

/-- Lean 可以自动判断：B 此时可以出【闪】。 -/
example : legal dodgeState (Command.useDodge PlayerId.b) := by
  decide

/-- B 出【闪】后，待结算的【杀】被清空。 -/
example :
    (useDodgeUnchecked dodgeState PlayerId.b).pendingSlash = none := by
  decide

/-- B 出【闪】后，处理区的【杀】和手牌里的【闪】都会进入弃牌堆，所以弃牌堆共有 2 张牌。 -/
example :
    (useDodgeUnchecked dodgeState PlayerId.b).discardPile.total = 2 := by
  decide

/--
例 3：A 受伤且手里有一张【桃】。

这个局面用来演示【桃】的合法性和回复效果。
-/
def peachState : GameState :=
  { current := PlayerId.a
    phase := Phase.play
    timing := Timing.idle
    playerA := { hp := 3, maxHp := 4, hand := { CardPool.empty with peach := 1 } }
    playerB := { hp := 4, maxHp := 4, hand := CardPool.empty } }

/-- A 受伤且手里有【桃】，所以 A 对自己使用【桃】合法。 -/
example : legal peachState (Command.usePeach PlayerId.a PlayerId.a) := by
  decide

/-- A 使用【桃】后，体力从 3 回复到 4。 -/
example :
    (usePeachUnchecked peachState PlayerId.a PlayerId.a).playerA.hp = 4 := by
  decide

end SanguoshaNew
