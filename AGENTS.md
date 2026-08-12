# type-pm-mech repository rules

プロジェクト固有の設計規律，文書同期，検証方法は`CLAUDE.md`に従う．

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
