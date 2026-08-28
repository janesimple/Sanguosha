import SanguoshaNew.Card

namespace SanguoshaNew

/-
这个文件描述“局面”。

形式化规则时，最重要的问题是：Lean 看到的游戏状态到底包含什么？
这里我们把局面拆成三层：

1. `CardPool`：某个区域里各种牌各有多少张。
2. `PlayerState`：一名玩家的体力、手牌、装备区、判定区。
3. `GameState`：整个游戏的当前玩家、阶段、各个公共牌区和待结算事件。

第一版使用“计数模型”，也就是只记【杀】有几张、【闪】有几张。
这样很容易证明牌数守恒。以后如果要研究牌堆顺序或具体牌面，
可以把这里替换成列表模型。
-/

/--
按种类计数的牌池。

例如一个人的手牌区可以写成：
`{ CardPool.empty with slash := 1, peach := 1 }`
表示他有一张【杀】和一张【桃】。
-/
structure CardPool where
  /-- 【杀】类牌数量。当前把普通杀、火杀、雷杀都计入这里。 -/
  slash : Nat := 0
  /-- 【闪】数量。 -/
  dodge : Nat := 0
  /-- 【桃】数量。 -/
  peach : Nat := 0
  /-- 【酒】数量。 -/
  wine : Nat := 0
  /-- 锦囊牌数量。当前只保留大类。 -/
  tactic : Nat := 0
  /-- 装备牌数量。当前只保留大类。 -/
  equipment : Nat := 0
  deriving Repr, DecidableEq

namespace CardPool

/-- 空牌池：所有牌数量都是 0。 -/
def empty : CardPool := {}

/--
查询某种牌有多少张。

注意：普通杀、火杀、雷杀目前都查询 `slash` 字段。
这是第一版的简化：先把它们当作“杀类资源”。
-/
def count (p : CardPool) : CardName -> Nat
  | CardName.basic BasicCard.slash => p.slash
  | CardName.basic BasicCard.fireSlash => p.slash
  | CardName.basic BasicCard.thunderSlash => p.slash
  | CardName.basic BasicCard.dodge => p.dodge
  | CardName.basic BasicCard.peach => p.peach
  | CardName.basic BasicCard.wine => p.wine
  | CardName.tactic => p.tactic
  | CardName.equipment => p.equipment

/--
给牌池增加一张指定牌。

这不是“摸牌”的完整规则，只是一个底层工具函数。
真正的摸牌动作以后会在规则层组合多个底层工具。
-/
def inc (p : CardPool) : CardName -> CardPool
  | CardName.basic BasicCard.slash => { p with slash := p.slash + 1 }
  | CardName.basic BasicCard.fireSlash => { p with slash := p.slash + 1 }
  | CardName.basic BasicCard.thunderSlash => { p with slash := p.slash + 1 }
  | CardName.basic BasicCard.dodge => { p with dodge := p.dodge + 1 }
  | CardName.basic BasicCard.peach => { p with peach := p.peach + 1 }
  | CardName.basic BasicCard.wine => { p with wine := p.wine + 1 }
  | CardName.tactic => { p with tactic := p.tactic + 1 }
  | CardName.equipment => { p with equipment := p.equipment + 1 }

/--
从牌池减少一张指定牌。

`Nat` 是自然数，没有负数，所以 `0 - 1` 仍然是 `0`。
因此调用 `dec` 前必须在规则层检查“确实有这张牌”。
这就是为什么 `Rules.lean` 里会有 `canUseSlash`、`canUseDodge` 等合法性判断。
-/
def dec (p : CardPool) : CardName -> CardPool
  | CardName.basic BasicCard.slash => { p with slash := p.slash - 1 }
  | CardName.basic BasicCard.fireSlash => { p with slash := p.slash - 1 }
  | CardName.basic BasicCard.thunderSlash => { p with slash := p.slash - 1 }
  | CardName.basic BasicCard.dodge => { p with dodge := p.dodge - 1 }
  | CardName.basic BasicCard.peach => { p with peach := p.peach - 1 }
  | CardName.basic BasicCard.wine => { p with wine := p.wine - 1 }
  | CardName.tactic => { p with tactic := p.tactic - 1 }
  | CardName.equipment => { p with equipment := p.equipment - 1 }

/-- 合并两个牌池。处理区牌结算完进入弃牌堆时会用到。 -/
def merge (x y : CardPool) : CardPool :=
  { slash := x.slash + y.slash
    dodge := x.dodge + y.dodge
    peach := x.peach + y.peach
    wine := x.wine + y.wine
    tactic := x.tactic + y.tactic
    equipment := x.equipment + y.equipment }

/-- 牌池里的总牌数。后面的不变量证明会大量使用它。 -/
def total (p : CardPool) : Nat :=
  p.slash + p.dodge + p.peach + p.wine + p.tactic + p.equipment

end CardPool

/-- 一名玩家当前的公开状态。 -/
structure PlayerState where
  /-- 玩家使用的武将；技能合法性检查会读取这个字段。 -/
  general : General := General.other
  /-- 当前体力值。这里用 `Nat`，所以最低是 0。 -/
  hp : Nat
  /-- 体力上限。 -/
  maxHp : Nat
  /-- 手牌区。 -/
  hand : CardPool := CardPool.empty
  /-- 装备区。第一版暂不实现装备效果，但先保留区域。 -/
  equipment : CardPool := CardPool.empty
  /-- 判定区。第一版暂不实现乐不思蜀、闪电等延时锦囊。 -/
  judgement : CardPool := CardPool.empty
  deriving Repr, DecidableEq

namespace PlayerState

/-- 玩家是否存活。 -/
def alive (p : PlayerState) : Prop := p.hp > 0
/-- 玩家是否处于濒死状态。第一版用 `hp = 0` 表示。 -/
def dying (p : PlayerState) : Prop := p.hp = 0
/-- 玩家是否受伤，即当前体力小于体力上限。 -/
def wounded (p : PlayerState) : Prop := p.hp < p.maxHp

/-- 判断这名玩家的武将在当前模型中是否拥有某个技能。 -/
def hasSkill (p : PlayerState) (skill : Skill) : Bool :=
  p.general.hasSkill skill

/-- 从手牌里移走一张牌。调用前应该先由合法性判断确认手里有牌。 -/
def loseFromHand (p : PlayerState) (c : CardName) : PlayerState :=
  { p with hand := p.hand.dec c }

/-- 往手牌里加入一张牌。当前示例还没实现摸牌流程，但先提供这个底层操作。 -/
def gainToHand (p : PlayerState) (c : CardName) : PlayerState :=
  { p with hand := p.hand.inc c }

/-- 受到若干点伤害。自然数减法会自动停在 0。 -/
def damage (amount : Nat) (p : PlayerState) : PlayerState :=
  { p with hp := p.hp - amount }

/-- 回复 1 点体力；如果已经满血，则不变。 -/
def healOne (p : PlayerState) : PlayerState :=
  if p.hp < p.maxHp then
    { p with hp := p.hp + 1 }
  else
    p

/-- 统计这名玩家所有私人区域中的牌数：手牌、装备区、判定区。 -/
def cardTotal (p : PlayerState) : Nat :=
  p.hand.total + p.equipment.total + p.judgement.total

end PlayerState

/--
待结算的【杀】。

在真实规则里，【杀】不是一使用就立即造成伤害。
目标有一个响应窗口，可以出【闪】。所以我们把“已经使用但还没结算完的杀”
存成 `PendingSlash`。
-/
structure PendingSlash where
  /-- 使用【杀】的玩家。 -/
  source : PlayerId
  /-- 被指定为目标的玩家。 -/
  target : PlayerId
  /-- 若最终命中，会造成的伤害值。普通情况是 1，喝酒后可能是 2。 -/
  damage : Nat
  deriving Repr, DecidableEq

/-- 整个游戏当前局面。 -/
structure GameState where
  /-- 当前回合的玩家。 -/
  current : PlayerId
  /-- 当前阶段。 -/
  phase : Phase
  /-- 当前时机。默认是空闲，表示没有特殊响应窗口。 -/
  timing : Timing := Timing.idle
  /-- A 玩家状态。 -/
  playerA : PlayerState
  /-- B 玩家状态。 -/
  playerB : PlayerState
  /-- 摸牌堆。第一版只记数量，不记顺序。 -/
  drawPile : CardPool := CardPool.empty
  /-- 弃牌堆。 -/
  discardPile : CardPool := CardPool.empty
  /-- 处理区：正在使用、尚未完全结算的牌。 -/
  processing : CardPool := CardPool.empty
  /-- 如果当前有一张【杀】等待响应，就放在这里；没有则为 `none`。 -/
  pendingSlash : Option PendingSlash := none
  /-- 当前出牌阶段已经使用过几张【杀】。第一版默认每阶段限一次。 -/
  slashUsed : Nat := 0
  /-- 当前出牌阶段是否已经主动使用过【酒】。 -/
  wineUsed : Bool := false
  /-- 是否存在“本回合下一张杀伤害 +1”的酒效果。 -/
  wineBuff : Bool := false
  deriving Repr, DecidableEq

namespace GameState

/-- 按玩家编号取得对应的玩家状态。 -/
def player (s : GameState) : PlayerId -> PlayerState
  | PlayerId.a => s.playerA
  | PlayerId.b => s.playerB

/--
更新某名玩家的状态。

Lean 的结构体默认不可原地修改，所以这里返回一个新的 `GameState`。
可以把它理解成：“旧局面基础上，替换其中一名玩家的数据”。
-/
def setPlayer (s : GameState) : PlayerId -> PlayerState -> GameState
  | PlayerId.a, p => { s with playerA := p }
  | PlayerId.b, p => { s with playerB := p }

/-- 当前回合玩家的状态。 -/
def activePlayer (s : GameState) : PlayerState :=
  s.player s.current

/-- 把处理区中的所有牌移入弃牌堆，并清空处理区。 -/
def putProcessingToDiscard (s : GameState) : GameState :=
  { s with
    discardPile := s.discardPile.merge s.processing
    processing := CardPool.empty }

/--
统计当前模型能看见的总牌数。

这个函数是证明“不凭空产生牌、不凭空消失牌”的基础。
目前统计玩家私人区域、摸牌堆、弃牌堆和处理区。
-/
def totalCards (s : GameState) : Nat :=
  s.playerA.cardTotal
    + s.playerB.cardTotal
    + s.drawPile.total
    + s.discardPile.total
    + s.processing.total

end GameState

end SanguoshaNew
