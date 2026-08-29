import SanguoshaNew.Invariant

namespace SanguoshaNew

/-!
这份文件放能直接运行的小例子。
它的作用不是补新规则，而是把课堂里常见的证明动作串起来：
先写一个具体局面，再用 `decide`、`rfl`、`simp` 看结论怎么被算出来。
-/

-- 例 1：A 出杀 B。
def oneSlashState : GameState :=
  { current := PlayerId.a
    phase := Phase.play
    timing := Timing.idle
    playerA := { hp := 4, maxHp := 4, hand := { CardPool.empty with slash := 1 } }
    playerB := { hp := 1, maxHp := 4, hand := CardPool.empty } }

-- 在这个局面里，A 对 B 出杀是合法的。
example : legal oneSlashState (Command.useSlash PlayerId.a PlayerId.b) := by
  decide

-- 合法命令会被 `transition` 原样算成对应的无检查执行。
example :
    transition oneSlashState (Command.useSlash PlayerId.a PlayerId.b)
      = some (useSlashUnchecked oneSlashState PlayerId.a PlayerId.b) := by
  rfl

-- B 没有出闪时，结算这张杀后会直接掉到 0 体力。
example :
    let afterSlash := useSlashUnchecked oneSlashState PlayerId.a PlayerId.b
    (settleSlashUnchecked afterSlash).playerB.hp = 0 := by
  decide

-- 例 2：B 正在响应 A 的杀。
def dodgeState : GameState :=
  { current := PlayerId.a
    phase := Phase.play
    timing := Timing.response
    playerA := { hp := 4, maxHp := 4, hand := CardPool.empty }
    playerB := { hp := 4, maxHp := 4, hand := { CardPool.empty with dodge := 1 } }
    processing := { CardPool.empty with slash := 1 }
    pendingSlash := some { source := PlayerId.a, target := PlayerId.b, damage := 1 } }

-- B 现在可以出闪。
example : legal dodgeState (Command.useDodge PlayerId.b) := by
  decide

-- 出闪后，待结算的杀会被清空。
example :
    (useDodgeUnchecked dodgeState PlayerId.b).pendingSlash = none := by
  decide

-- 出闪后，处理区和手牌里的牌都会进弃牌堆。
example :
    (useDodgeUnchecked dodgeState PlayerId.b).discardPile.total = 2 := by
  decide

-- 例 3：A 受伤并使用桃。
def peachState : GameState :=
  { current := PlayerId.a
    phase := Phase.play
    timing := Timing.idle
    playerA := { hp := 3, maxHp := 4, hand := { CardPool.empty with peach := 1 } }
    playerB := { hp := 4, maxHp := 4, hand := CardPool.empty } }

-- A 受伤且有桃，所以可以对自己使用桃。
example : legal peachState (Command.usePeach PlayerId.a PlayerId.a) := by
  decide

-- 使用桃后，A 的体力回到 4。
example :
    (usePeachUnchecked peachState PlayerId.a PlayerId.a).playerA.hp = 4 := by
  decide

-- 例 4：A 在自己的回合使用酒。
def wineState : GameState :=
  { current := PlayerId.a
    phase := Phase.play
    timing := Timing.idle
    playerA := { hp := 4, maxHp := 4, hand := { CardPool.empty with wine := 1 } }
    playerB := { hp := 4, maxHp := 4, hand := CardPool.empty } }

-- A 手里有一张酒，所以这条使用是合法的。
example : legal wineState (Command.useWine PlayerId.a) := by
  decide

-- A 使用酒后，会把酒状态记为 true。
example :
    (useWineUnchecked wineState PlayerId.a).wineBuff = true := by
  decide

-- 只要当前在出牌阶段，执行 `endPhase` 就会进入下一个阶段。
example :
    (endPhaseUnchecked oneSlashState).phase = Phase.discard := by
  decide

-- 没有待结算的【杀】时，不能直接结算。
example : transition oneSlashState Command.settlePendingSlash = none := by
  decide

-- 没有待结算的【杀】时，也不能响应出【闪】。
example : transition oneSlashState (Command.useDodge PlayerId.b) = none := by
  decide

-- 出牌阶段正常结束时，`transition` 会给出新的局面。
example :
    transition oneSlashState Command.endPhase
      = some (endPhaseUnchecked oneSlashState) := by
  rfl

end SanguoshaNew
