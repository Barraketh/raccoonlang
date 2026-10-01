# A paged fill into a ring of the wrong boxes: checks/paged_emitted.rac with one change. Run by check.sh through
# gpu/mutate.py. (The paged example's rings are the shared roles', encoding/Attention.rac, so its own table,
# paged_attention_mutants.py, cannot give a ring other boxes.)

SOURCE = "encoding/checks/paged_emitted.rac"

MUTANTS = [
    dict(
        name="half_page_box", expect="EvidenceNotDischarged", mentions="fillPage",
        why="Gives the V ring a second box of 64 rows. `fillPage` loads both boxes through the one cache map, whose "
            "box is the first's (a map of the wrong box is a type error), so the stage would expect bytes that do not "
            "match what lands. `fillPage` requires stages of two 64 × 128 boxes, one page of one head, at generation.",
        old="""  def vRing : RingCfg := RingCfg.mk(2, box, box)""",
        new="""  def vRing : RingCfg := RingCfg.mk(2, box, TmaSpec.mk(64, 64))""",
    ),
]
