import SanguoshaNew.Rules

namespace SanguoshaNew

/-
这个文件放“不变量证明”。

不变量可以理解为：无论规则怎么执行，都应该一直保持成立的性质。
本文件先证明最基础的一类不变量：牌数守恒。

例如使用【杀】时，一张【杀】从手牌进入处理区。
它的位置变了，但没有凭空消失，也没有凭空多出来。

对 Lean 新手来说，可以先把 theorem 看成“Lean 检查过的断言”：
如果下面的证明能通过 `lake build`，说明这个断言在当前模型里确实成立。
-/

/--
【桃】回复体力不会改变手牌区。

这个小引理标记了 `@[simp]`，意思是：以后 `simp` 化简时可以自动使用它。
-/
@[simp] theorem PlayerState.healOne_hand (p : PlayerState) :
    p.healOne.hand = p.hand := by
  unfold PlayerState.healOne
  by_cases h : p.hp < p.maxHp <;> simp [h]

/-- 【桃】回复体力不会改变装备区。 -/
@[simp] theorem PlayerState.healOne_equipment (p : PlayerState) :
    p.healOne.equipment = p.equipment := by
  unfold PlayerState.healOne
  by_cases h : p.hp < p.maxHp <;> simp [h]

/-- 【桃】回复体力不会改变判定区。 -/
@[simp] theorem PlayerState.healOne_judgement (p : PlayerState) :
    p.healOne.judgement = p.judgement := by
  unfold PlayerState.healOne
  by_cases h : p.hp < p.maxHp <;> simp [h]

/--
A 对 B 使用【杀】时，总牌数不变。

前提 `h` 表示 A 的手牌里确实至少有一张【杀】。
证明思路很朴素：A 手牌里的【杀】少 1，处理区里的【杀】多 1。
-/
theorem useSlashA_preserves_totalCards
    (s : GameState)
    (h : s.playerA.hand.slash > 0) :
    (useSlashUnchecked s PlayerId.a PlayerId.b).totalCards = s.totalCards := by
  cases s
  simp [useSlashUnchecked, removeHandCardToProcessing, GameState.totalCards,
    GameState.setPlayer, GameState.player, PlayerState.cardTotal,
    PlayerState.loseFromHand, CardPool.dec, CardPool.inc, CardPool.total,
    CardName.slash, slashDamageFromWine] at *
  omega

/--
B 对 A 使用【杀】时，总牌数不变。

这个定理和上一个对称，只是换了玩家方向。
-/
theorem useSlashB_preserves_totalCards
    (s : GameState)
    (h : s.playerB.hand.slash > 0) :
    (useSlashUnchecked s PlayerId.b PlayerId.a).totalCards = s.totalCards := by
  cases s
  simp [useSlashUnchecked, removeHandCardToProcessing, GameState.totalCards,
    GameState.setPlayer, GameState.player, PlayerState.cardTotal,
    PlayerState.loseFromHand, CardPool.dec, CardPool.inc, CardPool.total,
    CardName.slash, slashDamageFromWine] at *
  omega

/--
A 使用【闪】响应时，总牌数不变。

当前模型中，【闪】从 A 的手牌进入弃牌堆；
同时处理区中正在结算的【杀】也进入弃牌堆。
这些都是移动牌的位置，不会改变总数。
-/
theorem dodgeA_preserves_totalCards
    (s : GameState)
    (h : s.playerA.hand.dodge > 0) :
    (useDodgeUnchecked s PlayerId.a).totalCards = s.totalCards := by
  cases s
  simp [useDodgeUnchecked, removeHandCardToDiscard, GameState.putProcessingToDiscard,
    GameState.totalCards, GameState.setPlayer, GameState.player,
    PlayerState.cardTotal, PlayerState.loseFromHand, CardPool.dec,
    CardPool.inc, CardPool.merge, CardPool.total, CardPool.empty,
    CardName.dodge] at *
  omega

/--
A 对自己使用【桃】时，总牌数不变。

【桃】会改变体力，但牌的部分只是“手牌少 1、弃牌堆多 1”。
上面的 `healOne_*` 引理帮助 Lean 明白：回血不会改变各个牌区。
-/
theorem peachA_preserves_totalCards
    (s : GameState)
    (h : s.playerA.hand.peach > 0) :
    (usePeachUnchecked s PlayerId.a PlayerId.a).totalCards = s.totalCards := by
  cases s
  simp [usePeachUnchecked, removeHandCardToDiscard, GameState.totalCards,
    GameState.setPlayer, GameState.player, PlayerState.cardTotal,
    PlayerState.loseFromHand, CardPool.dec,
    CardPool.inc, CardPool.total, CardName.peach] at *
  omega

/-
下面开始证明“任意成功操作都保持牌量守恒”。

思路是先给每种底层操作证明一个通用引理：
* 任意玩家用【杀】：手牌少一张杀，处理区多一张杀；
* 任意玩家出【闪】：手牌少一张闪，弃牌堆多一张闪，处理区进入弃牌堆；
* 任意玩家用【桃】：手牌少一张桃，弃牌堆多一张桃，回血不影响牌区；
* 任意玩家用【酒】：手牌少一张酒，弃牌堆多一张酒，酒标记和回血不影响牌区；
* 结算【杀】：处理区进入弃牌堆，伤害不影响牌区；
* 结束阶段：只改阶段/玩家/次数标记，不影响牌区。

最后把这些引理合并成 `transition_preserves_totalCards`。
-/

/-- 受到伤害只改变体力，不改变手牌区。 -/
@[simp] theorem PlayerState.damage_hand (p : PlayerState) (amount : Nat) :
    (p.damage amount).hand = p.hand := by
  simp [PlayerState.damage]

/-- 受到伤害只改变体力，不改变装备区。 -/
@[simp] theorem PlayerState.damage_equipment (p : PlayerState) (amount : Nat) :
    (p.damage amount).equipment = p.equipment := by
  simp [PlayerState.damage]

/-- 受到伤害只改变体力，不改变判定区。 -/
@[simp] theorem PlayerState.damage_judgement (p : PlayerState) (amount : Nat) :
    (p.damage amount).judgement = p.judgement := by
  simp [PlayerState.damage]

/-- 任意玩家使用【杀】时，总牌数不变。 -/
theorem useSlashUnchecked_preserves_totalCards
    (s : GameState)
    (source target : PlayerId)
    (h : (s.player source).hand.count CardName.slash > 0) :
    (useSlashUnchecked s source target).totalCards = s.totalCards := by
  cases source <;> cases target <;> cases s
  all_goals
    simp [useSlashUnchecked, removeHandCardToProcessing, GameState.totalCards,
      GameState.setPlayer, GameState.player, PlayerState.cardTotal,
      PlayerState.loseFromHand, CardPool.dec, CardPool.inc, CardPool.total,
      CardPool.count, CardName.slash, slashDamageFromWine] at *
    omega

/-- 任意玩家使用【闪】响应时，总牌数不变。 -/
theorem useDodgeUnchecked_preserves_totalCards
    (s : GameState)
    (responder : PlayerId)
    (h : (s.player responder).hand.count CardName.dodge > 0) :
    (useDodgeUnchecked s responder).totalCards = s.totalCards := by
  cases responder <;> cases s
  all_goals
    simp [useDodgeUnchecked, removeHandCardToDiscard, GameState.putProcessingToDiscard,
      GameState.totalCards, GameState.setPlayer, GameState.player,
      PlayerState.cardTotal, PlayerState.loseFromHand, CardPool.dec,
      CardPool.inc, CardPool.merge, CardPool.total, CardPool.empty,
      CardPool.count, CardName.dodge] at *
    omega

/-- 任意玩家使用【桃】时，总牌数不变。 -/
theorem usePeachUnchecked_preserves_totalCards
    (s : GameState)
    (source target : PlayerId)
    (h : (s.player source).hand.count CardName.peach > 0) :
    (usePeachUnchecked s source target).totalCards = s.totalCards := by
  cases source <;> cases target <;> cases s
  all_goals
    simp [usePeachUnchecked, removeHandCardToDiscard, GameState.totalCards,
      GameState.setPlayer, GameState.player, PlayerState.cardTotal,
      PlayerState.loseFromHand, CardPool.dec, CardPool.inc, CardPool.total,
      CardPool.count, CardName.peach] at *
    omega

/-- 任意玩家使用【酒】时，总牌数不变。 -/
theorem useWineUnchecked_preserves_totalCards
    (s : GameState)
    (source : PlayerId)
    (h : (s.player source).hand.count CardName.wine > 0) :
    (useWineUnchecked s source).totalCards = s.totalCards := by
  cases source with
  | a =>
      cases s with
      | mk current phase timing playerA playerB drawPile discardPile processing pendingSlash slashUsed wineUsed wineBuff =>
          simp [useWineUnchecked, removeHandCardToDiscard, GameState.totalCards,
            GameState.setPlayer, GameState.player, PlayerState.cardTotal,
            PlayerState.loseFromHand, CardPool.dec, CardPool.inc, CardPool.total,
            CardPool.count, CardName.wine] at h ⊢
          by_cases hdy : playerA.hp = 0
          · simp [hdy] at *
            omega
          · simp [hdy] at *
            omega
  | b =>
      cases s with
      | mk current phase timing playerA playerB drawPile discardPile processing pendingSlash slashUsed wineUsed wineBuff =>
          simp [useWineUnchecked, removeHandCardToDiscard, GameState.totalCards,
            GameState.setPlayer, GameState.player, PlayerState.cardTotal,
            PlayerState.loseFromHand, CardPool.dec, CardPool.inc, CardPool.total,
            CardPool.count, CardName.wine] at h ⊢
          by_cases hdy : playerB.hp = 0
          · simp [hdy] at *
            omega
          · simp [hdy] at *
            omega

/-- 处理区全部进入弃牌堆时，总牌数不变。 -/
theorem putProcessingToDiscard_preserves_totalCards
    (s : GameState) :
    s.putProcessingToDiscard.totalCards = s.totalCards := by
  cases s
  simp [GameState.putProcessingToDiscard, GameState.totalCards, PlayerState.cardTotal,
    CardPool.merge, CardPool.empty, CardPool.total]
  omega

/-- 结算待处理【杀】时，总牌数不变。 -/
theorem settleSlashUnchecked_preserves_totalCards
    (s : GameState) :
    (settleSlashUnchecked s).totalCards = s.totalCards := by
  cases s with
  | mk current phase timing playerA playerB drawPile discardPile processing pendingSlash slashUsed wineUsed wineBuff =>
      cases pendingSlash with
      | none =>
          simp [settleSlashUnchecked]
      | some pending =>
          cases pending with
          | mk source target damage =>
              cases target
              all_goals
                simp [settleSlashUnchecked, GameState.putProcessingToDiscard,
                  GameState.totalCards, GameState.setPlayer, GameState.player,
                  PlayerState.cardTotal, PlayerState.damage, CardPool.merge,
                  CardPool.empty, CardPool.total]
                omega

/-- 结束阶段或换人时，总牌数不变。 -/
theorem endPhaseUnchecked_preserves_totalCards
    (s : GameState) :
    (endPhaseUnchecked s).totalCards = s.totalCards := by
  by_cases h : s.phase = Phase.finish
  · simp [endPhaseUnchecked, h, GameState.totalCards]
  · simp [endPhaseUnchecked, h, GameState.totalCards]

/--
总定理：任意成功执行的命令都保持总牌数不变。

这里的“任意操作”指当前 `Command` 中已经建模的所有命令。
非法命令会返回 `none`，没有新局面；只要返回 `some s'`，
新旧局面的 `totalCards` 就相等。
-/
theorem transition_preserves_totalCards
    (s : GameState)
    (c : Command)
    (s' : GameState)
    (htrans : transition s c = some s') :
    s'.totalCards = s.totalCards := by
  unfold transition at htrans
  by_cases hlegal : legal s c
  · simp [hlegal] at htrans
    cases c with
    | useSlash source target =>
        simp at htrans
        subst s'
        unfold legal canUseSlash at hlegal
        rcases hlegal with ⟨_, _, _, _, _, _, _, hcard, _⟩
        exact useSlashUnchecked_preserves_totalCards s source target hcard
    | useDodge responder =>
        simp at htrans
        subst s'
        unfold legal canUseDodge at hlegal
        cases hpending : s.pendingSlash with
        | none =>
            simp [hpending] at hlegal
        | some pending =>
            simp [hpending, PlayerState.alive] at hlegal
            rcases hlegal with ⟨_, _, hcard⟩
            exact useDodgeUnchecked_preserves_totalCards s responder hcard
    | usePeach source target =>
        simp at htrans
        subst s'
        unfold legal canUsePeach at hlegal
        rcases hlegal with ⟨_, _, _, _, _, _, _, hcard⟩
        exact usePeachUnchecked_preserves_totalCards s source target hcard
    | useWine source =>
        simp at htrans
        subst s'
        unfold legal canUseWine at hlegal
        rcases hlegal with hactive | hdying
        · rcases hactive with ⟨_, _, _, _, _, _, hcard⟩
          exact useWineUnchecked_preserves_totalCards s source hcard
        · rcases hdying with ⟨_, hcard⟩
          exact useWineUnchecked_preserves_totalCards s source hcard
    | settlePendingSlash =>
        simp at htrans
        subst s'
        exact settleSlashUnchecked_preserves_totalCards s
    | endPhase =>
        simp at htrans
        subst s'
        exact endPhaseUnchecked_preserves_totalCards s
  · simp [hlegal] at htrans

end SanguoshaNew
