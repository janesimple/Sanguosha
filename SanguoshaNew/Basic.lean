namespace SanguoshaNew

/-
这个文件只放最基础的“名词”。

Lean 里的 `inductive` 可以理解成“列举一种概念有哪些可能情况”。
例如 `Phase` 就是在告诉 Lean：三国杀的回合阶段只可能是下面六种之一。
-/

/-- 回合的六个阶段。这里先只记录阶段名称，不处理每个阶段内部的复杂细节。 -/
inductive Phase where
  /-- 准备阶段。 -/
  | prepare
  /-- 判定阶段。 -/
  | judge
  /-- 摸牌阶段。 -/
  | draw
  /-- 出牌阶段。大部分主动使用牌的行为先放在这个阶段里。 -/
  | play
  /-- 弃牌阶段。当前框架还没有实现手牌上限弃牌。 -/
  | discard
  /-- 结束阶段。 -/
  | finish
  deriving Repr, DecidableEq

/--
粗粒度的“时机”。

`Phase` 说明现在处在哪个阶段；`Timing` 说明现在是否正处于某个特殊窗口。
例如 `phase = play` 且 `timing = response` 可以表示：仍在出牌阶段，
但现在不是随便出牌的时候，而是在等待某人响应一张【杀】。
-/
inductive Timing where
  /-- 回合开始前。 -/
  | beforeTurn
  /-- 某个阶段刚开始。 -/
  | phaseStart
  /-- 空闲时机：没有待响应或待结算事件，可以正常行动。 -/
  | idle
  /-- 某个阶段即将结束。 -/
  | phaseEnd
  /-- 回合结束后。 -/
  | afterTurn
  /-- 响应窗口，例如目标需要对【杀】出【闪】。 -/
  | response
  /-- 结算窗口，例如无人响应后执行伤害。 -/
  | settlement
  deriving Repr, DecidableEq

/--
牌可能所在的区域。

真实游戏里还有更多细分区域和临时移动过程。这里先列出足够支撑
基础牌结算的区域。
-/
inductive Zone where
  /-- 摸牌堆。当前只记录数量，没有记录牌堆顺序。 -/
  | drawPile
  /-- 弃牌堆。 -/
  | discardPile
  /-- 处理区：正在使用或结算中的牌会先放在这里。 -/
  | processing
  /-- 手牌区。 -/
  | hand
  /-- 装备区。当前只预留区域，暂未实现装备效果。 -/
  | equipment
  /-- 判定区。当前只预留区域，暂未实现延时锦囊。 -/
  | judgement
  deriving Repr, DecidableEq

/--
玩家编号。

为了让第一版证明简单清楚，先只建模两名玩家 `a` 和 `b`。
多人局、身份局和座次距离可以以后在这里扩展。
-/
inductive PlayerId where
  | a
  | b
  deriving Repr, DecidableEq

namespace PlayerId

/-- 两人局里，“下一个玩家”就是另一个玩家。 -/
def next : PlayerId -> PlayerId
  | a => b
  | b => a

end PlayerId

/-- 当前模型中与判定牌改判相关的武将技能。 -/
inductive Skill where
  /-- 【鬼才】：司马懿可以用一张手牌替换当前判定牌。 -/
  | guicai
  /-- 【鬼道】：张角可以用一张黑色牌替换当前判定牌。 -/
  | guidao
  /-- 【自书】：马良的锁定技，本回合内获得非【自书】牌后会额外摸一张牌。 -/
  | zishu
  /-- 【应援】：马良的主动技，可以把本回合使用过并进入弃牌堆的牌交给其他角色。 -/
  | yingyuan
  /-- 【镇骨】：郝昭的技能；当前六伤证明只登记技能包，不展开其回合结束结算。 -/
  | zhengu
  /-- 【慧识】：神郭嘉的技能；当前六伤证明不把它建模为防御技能。 -/
  | shenHuishi
  /-- 【天翊】：神郭嘉的技能；当前六伤证明不把它建模为防御技能。 -/
  | tianyi
  /-- 【辉逝】：神郭嘉的技能；当前六伤证明不把它建模为防御技能。 -/
  | huiShiFarewell
  deriving Repr, DecidableEq

/-- 当前形式化模型需要区分的武将。 -/
inductive General where
  | other
  | zhangJiao
  | simaYi
  | maLiang
  | haoZhao
  | shenGuojia
  deriving Repr, DecidableEq

namespace General

/-- 当前模型中每名武将拥有的技能列表。 -/
def skills : General -> List Skill
  | General.zhangJiao => [Skill.guidao]
  | General.simaYi => [Skill.guicai]
  | General.maLiang => [Skill.zishu, Skill.yingyuan]
  | General.haoZhao => [Skill.zhengu]
  | General.shenGuojia => [Skill.shenHuishi, Skill.tianyi, Skill.huiShiFarewell]
  | General.other => []

/-- 查询一名武将是否拥有某个技能；返回 `Bool` 便于示例中用 `decide` 自动计算。 -/
def hasSkill (g : General) (skill : Skill) : Bool :=
  g.skills.any (fun owned => if owned = skill then true else false)

end General

end SanguoshaNew
