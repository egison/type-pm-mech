# type-pm-mech repository rules

プロジェクト固有の設計規律，文書同期，検証方法は`CLAUDE.md`に従う．

## 論文中の program を検査する回帰

- `../type-pm-paper/` に掲載する executable program は，対応する名前付き regression を
  `TypePM/` に置き，意図した型，成功／通常の不一致，探索順，出現位置ごとの分岐の多重性を検査する．
- 型安全性の証拠として使う program は，公開 inference から `SourceTyping`，正確な
  `evalFuel`，`evalFuel_ok`，適用可能な all-fuel no-stuck まで接続する．
- 論文の program を追加・変更したときは対応回帰も同時に確認する．現行 core で表現できない場合は
  機械化済みと扱わず，README の roadmap と論文の範囲記述に不足を明記する．

## Git

このリポジトリは親ワークスペースの「commit／pushにはその都度の明示指示が必要」という規則の
例外である．まとまりのある変更が完了し，`CLAUDE.md`が要求する検証が通った時点で，個別の指示を
待たずに適宜commitし，現在のbranchをpushする．

- 大きな作業では，独立して検証できる意味のある区切りごとにcommit／pushしてよい．
- 未完成・未検証の状態を単に保存するcommitは作らない．
- ユーザーの無関係な変更をcommitに混ぜない．安全に分離できない場合，検証が失敗している場合，
  またはpush先が不明な場合はcommit／pushせず状況を報告する．
- commit messageに`Co-Authored-By`行を付けない．
- ユーザーがその作業についてcommit／pushしないよう明示した場合は，その指示を優先する．
