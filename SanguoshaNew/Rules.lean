import SanguoshaNew.State

namespace SanguoshaNew

/-
这个文件描述“规则”。

本工程把规则分成两步：

1. `canUse...` / `legal`：判断某个行动在当前局面下是否合法。
2. `...Unchecked` / `transition`：真正计算行动后的新局面。

为什么要分开？
因为三国杀里“有这个动作”和“现在能不能做这个动作”是两回事。
例如玩家当然可以想“出杀”，但如果不在出牌阶段、手里没有杀、
或者这一阶段已经出过杀，那么这个动作就不合法。
-/

/--
玩家可以发出的命令。

这里的命令是“玩家意图”，不是保证能执行的合法行动。
例如 `useSlash a b` 只是说 A 想对 B 使用【杀】。
它是否合法，要交给 `legal` 判断。
-/
inductive Command where
  /-- 使用【杀】：`source` 是使用者，`target` 是目标。 -/
  | useSlash (source target : PlayerId)
  /-- 使用【闪】：只在响应【杀】时有效。 -/
  | useDodge (responder : PlayerId)
  /-- 使用【桃】：`source` 是使用者，`target` 是回复体力的人。 -/
  | usePeach (source target : PlayerId)
  /-- 使用【酒】：出牌阶段可强化下一张【杀】，濒死时可自救。 -/
  | useWine (source : PlayerId)
  /-- 结算一张没有被【闪】抵消的待处理【杀】。 -/
  | settlePendingSlash
  /-- 结束当前阶段，进入下一个阶段。 -/
  | endPhase
  deriving Repr, DecidableEq

/-- 当前是否没有待响应、待结算的【杀】。 -/
def noPending (s : GameState) : Prop :=
  s.pendingSlash = none

/--
判断能否使用【杀】。

当前简化规则：
* 必须在出牌阶段；
* 当前没有响应窗口；
* 使用者必须是当前回合玩家；
* 不能杀自己；
* 双方都必须存活；
* 使用者手里至少有一张【杀】；
* 当前出牌阶段还没用过【杀】。
-/
def canUseSlash (s : GameState) (source target : PlayerId) : Prop :=
  s.phase = Phase.play
    ∧ s.timing = Timing.idle
    ∧ noPending s
    ∧ s.current = source
    ∧ source ≠ target
    ∧ (s.player source).alive
    ∧ (s.player target).alive
    ∧ (s.player source).hand.count CardName.slash > 0
    ∧ s.slashUsed < 1

/--
判断能否使用【闪】。

【闪】不是在空闲时随便使用的牌。当前模型要求：
* 局面里存在一张待响应的【杀】；
* 这张【杀】的目标正是出闪者；
* 出闪者还活着；
* 出闪者手里至少有一张【闪】。
-/
def canUseDodge (s : GameState) (responder : PlayerId) : Prop :=
  match s.pendingSlash with
  | none => False
  | some pending =>
      pending.target = responder
        ∧ (s.player responder).alive
        ∧ (s.player responder).hand.count CardName.dodge > 0

/--
判断能否使用【桃】。

当前简化规则只实现出牌阶段对存活角色使用【桃】回复 1 点体力。
濒死求桃、其他角色救援等更复杂规则后续再加。
-/
def canUsePeach (s : GameState) (source target : PlayerId) : Prop :=
  s.phase = Phase.play
    ∧ s.timing = Timing.idle
    ∧ noPending s
    ∧ s.current = source
    ∧ (s.player source).alive
    ∧ (s.player target).alive
    ∧ (s.player target).wounded
    ∧ (s.player source).hand.count CardName.peach > 0

/--
判断能否使用【酒】。

这里覆盖两种情况：
* 出牌阶段主动使用：本阶段未用过酒，获得下一张【杀】伤害 +1；
* 濒死自救：自己体力为 0 时，可以用酒回复 1 点体力。

注意：第一版暂不处理“其他人能否用酒救你”等扩展规则。
-/
def canUseWine (s : GameState) (source : PlayerId) : Prop :=
  (s.current = source
    ∧ s.phase = Phase.play
    ∧ s.timing = Timing.idle
    ∧ noPending s
    ∧ (s.player source).alive
    ∧ s.wineUsed = false
    ∧ (s.player source).hand.count CardName.wine > 0)
  ∨ ((s.player source).dying
    ∧ (s.player source).hand.count CardName.wine > 0)

/-- 判断当前是否有待结算的【杀】。 -/
def canSettlePendingSlash (s : GameState) : Prop :=
  match s.pendingSlash with
  | none => False
  | some _pending => True

/--
统一的合法性入口。

以后新增命令时，只要在这里增加一行映射，就能让 `transition`
继续用同一个合法性检查入口。
-/
def legal (s : GameState) : Command -> Prop
  | Command.useSlash source target => canUseSlash s source target
  | Command.useDodge responder => canUseDodge s responder
  | Command.usePeach source target => canUsePeach s source target
  | Command.useWine source => canUseWine s source
  | Command.settlePendingSlash => canSettlePendingSlash s
  | Command.endPhase => s.pendingSlash = none

/--
告诉 Lean：这些合法性条件都是可以自动判断真假的。

`Prop` 是命题，比如“玩家手里有杀”。Lean 默认不一定知道一个命题
能不能机械判断。这里的规则只涉及等号、自然数大小比较、有限枚举，
所以可以让 Lean 自动决定。
-/
instance (s : GameState) (c : Command) : Decidable (legal s c) := by
  cases c with
  | useSlash source target =>
      unfold legal canUseSlash noPending PlayerState.alive
      infer_instance
  | useDodge responder =>
      unfold legal canUseDodge PlayerState.alive
      cases s.pendingSlash <;> infer_instance
  | usePeach source target =>
      unfold legal canUsePeach noPending PlayerState.alive PlayerState.wounded
      infer_instance
  | useWine source =>
      unfold legal canUseWine noPending PlayerState.alive PlayerState.dying
      infer_instance
  | settlePendingSlash =>
      unfold legal canSettlePendingSlash
      cases s.pendingSlash <;> infer_instance
  | endPhase =>
      unfold legal
      infer_instance

/-- 如果有酒的强化效果，下一张【杀】造成 2 点伤害；否则造成 1 点。 -/
def slashDamageFromWine (s : GameState) : Nat :=
  if s.wineBuff then 2 else 1

/--
从某玩家手牌移走一张牌，放入处理区。

使用【杀】时，牌会先进入处理区，因为它还在等待目标是否出【闪】。
-/
def removeHandCardToProcessing
    (s : GameState) (source : PlayerId) (card : CardName) : GameState :=
  let p := (s.player source).loseFromHand card
  { s.setPlayer source p with processing := s.processing.inc card }

/--
从某玩家手牌移走一张牌，直接放入弃牌堆。

例如【闪】响应成功后会进入弃牌堆；【桃】和【酒】使用后也直接进弃牌堆。
-/
def removeHandCardToDiscard
    (s : GameState) (source : PlayerId) (card : CardName) : GameState :=
  let p := (s.player source).loseFromHand card
  { s.setPlayer source p with discardPile := s.discardPile.inc card }

/--
不检查合法性，直接执行“使用【杀】”的局面变化。

`Unchecked` 的意思是：这个函数假设调用者已经检查过合法性。
普通外部调用应该使用 `transition`，不要直接用这个函数。

执行效果：
* 使用者手牌中的一张【杀】进入处理区；
* 创建一个 `pendingSlash`，等待目标响应；
* 时机变成 `response`；
* 本阶段使用【杀】次数 +1；
* 酒的强化效果被消耗。
-/
def useSlashUnchecked (s : GameState) (source target : PlayerId) : GameState :=
  let s1 := removeHandCardToProcessing s source CardName.slash
  { s1 with
    pendingSlash := some { source := source, target := target, damage := slashDamageFromWine s }
    timing := Timing.response
    slashUsed := s.slashUsed + 1
    wineBuff := false }

/--
不检查合法性，直接执行“使用【闪】”。

执行效果：
* 响应者手牌中的一张【闪】进入弃牌堆；
* 处理区里的【杀】也进入弃牌堆；
* 清空待结算【杀】；
* 回到空闲时机。
-/
def useDodgeUnchecked (s : GameState) (responder : PlayerId) : GameState :=
  let s1 := removeHandCardToDiscard s responder CardName.dodge
  { s1.putProcessingToDiscard with
    pendingSlash := none
    timing := Timing.idle }

/--
不检查合法性，直接结算待处理【杀】。

如果没有待结算【杀】，函数返回原局面。
如果有，就让目标受到记录的伤害，然后把处理区的牌放入弃牌堆。
-/
def settleSlashUnchecked (s : GameState) : GameState :=
  match s.pendingSlash with
  | none => s
  | some pending =>
      let damaged := (s.player pending.target).damage pending.damage
      { (s.setPlayer pending.target damaged).putProcessingToDiscard with
        pendingSlash := none
        timing := Timing.idle }

/--
不检查合法性，直接执行“使用【桃】”。

当前模型里，【桃】会从使用者手牌进入弃牌堆，并让目标回复 1 点体力。
-/
def usePeachUnchecked (s : GameState) (source target : PlayerId) : GameState :=
  let s1 := removeHandCardToDiscard s source CardName.peach
  let healed := (s1.player target).healOne
  s1.setPlayer target healed

/--
不检查合法性，直接执行“使用【酒】”。

如果使用者濒死，则回复 1 点体力。
否则记录“本阶段已用酒”，并打开 `wineBuff`，让下一张【杀】伤害 +1。
-/
def useWineUnchecked (s : GameState) (source : PlayerId) : GameState :=
  let s1 := removeHandCardToDiscard s source CardName.wine
  if (s.player source).hp = 0 then
    let healed := (s1.player source).healOne
    s1.setPlayer source healed
  else
    { s1 with wineUsed := true, wineBuff := true }

/-- 阶段顺序。结束阶段之后回到准备阶段，配合换人进入下一个回合。 -/
def nextPhase : Phase -> Phase
  | Phase.prepare => Phase.judge
  | Phase.judge => Phase.draw
  | Phase.draw => Phase.play
  | Phase.play => Phase.discard
  | Phase.discard => Phase.finish
  | Phase.finish => Phase.prepare

/--
不检查合法性，直接结束当前阶段。

如果当前是结束阶段，则切换到下一名玩家并重置每回合限制；
否则只进入下一个阶段。
-/
def endPhaseUnchecked (s : GameState) : GameState :=
  if s.phase = Phase.finish then
    { s with
      current := s.current.next
      phase := Phase.prepare
      slashUsed := 0
      wineUsed := false
      wineBuff := false
      timing := Timing.idle }
  else
    { s with phase := nextPhase s.phase, timing := Timing.idle }

/--
安全的规则入口。

`transition s c` 表示“在局面 `s` 下尝试执行命令 `c`”。

返回值是 `Option GameState`：
* `some s2` 表示命令合法，并得到新局面 `s2`；
* `none` 表示命令非法，局面不应该变化。

这比直接返回 `GameState` 更安全，因为它强迫我们处理非法行动。
-/
-- 规则层最终只暴露一个安全入口：先判合法性，再决定是否执行。
def transition (s : GameState) (c : Command) : Option GameState :=
  if legal s c then
    match c with
    | Command.useSlash source target => some (useSlashUnchecked s source target)
    | Command.useDodge responder => some (useDodgeUnchecked s responder)
    | Command.usePeach source target => some (usePeachUnchecked s source target)
    | Command.useWine source => some (useWineUnchecked s source)
    | Command.settlePendingSlash => some (settleSlashUnchecked s)
    | Command.endPhase => some (endPhaseUnchecked s)
  else
    none

end SanguoshaNew

namespace SanguoshaNew

/--
`transition` 返回 `none` 当且仅当命令不合法。
这条引理把“先检查合法性，再决定是否执行”明确写成了双向结论。
-/
theorem transition_eq_none_iff_not_legal (s : GameState) (c : Command) :
    transition s c = none ↔ ¬ legal s c := by
  constructor
  · intro hnone hlegal
    cases c <;> simp [transition, hlegal] at hnone
  · intro hnot
    by_cases hlegal : legal s c
    · exact False.elim (hnot hlegal)
    · cases c <;> simp [transition, hlegal]

/--
只要 `transition` 成功返回了某个新局面，就说明这条命令原本是合法的。
这在反推前提时很有用，尤其适合配合 `cases` 和 `simp` 一起拆分分支。
-/
theorem legal_of_transition_some
    (s : GameState) (c : Command) (s' : GameState)
    (h : transition s c = some s') :
    legal s c := by
  by_cases hs : legal s c
  · exact hs
  · simp [transition, hs] at h
end SanguoshaNew
