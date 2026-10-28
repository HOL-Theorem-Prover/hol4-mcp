"""In-memory rewind points: a rewind restores Context, loaded modules and the
names bound since, without a SaveState load; it falls back to a SaveState file
across an opaque span (SML refs a point does not cover) or a module load."""
from hol4_mcp.hol_mcp_server import (
    _init_file_cursor,
    _sessions,
    hol_send,
    hol_state_at,
    hol_stop,
)

THREE_SCRIPT = """\
open HolKernel Parse boolLib bossLib;

val _ = new_theory "rwp";

val counter = ref 0;

Theorem a_thm:
  T
Proof
  simp[]
QED

val _ = counter := !counter + 1;{marker}

Theorem b_thm:
  T /\\ T
Proof
  simp[]
QED

Theorem c_thm:
  T \\/ F
Proof
  simp[]
QED

Theorem d_thm:
  ~F
Proof
  simp[]
QED

val _ = export_theory();
"""
OPAQUE_MARKER = "  (* stands in for a translate call *)"


def _script(tmp_path, marker=""):
    path = tmp_path / "rwpScript.sml"
    path.write_text(THREE_SCRIPT.replace("{marker}", marker))
    return path


async def _edit_b_and_return(script, session):
    script.write_text(script.read_text().replace("T /\\ T", "T /\\ T /\\ T"))
    return await hol_state_at(line=24, col=3, session=session)


async def test_rewind_uses_a_point_and_unbinds_later_names(tmp_path):
    script = _script(tmp_path)
    session = "rwp_point"
    try:
        await _init_file_cursor(file=str(script), session=session)
        await hol_state_at(line=30, col=3, session=session)   # inside d_thm
        cursor = _sessions[session].cursor
        assert cursor._checkpoints["a_thm"].point_id is not None
        state = await _edit_b_and_return(script, session)       # into c_thm
        assert "=== Goal" in state and "Session reinit" not in state, state
        # c_thm ran after the point and has not run since the rewind.
        assert "unit" in await hol_send("c_thm;", session=session)
        # A plain ref outside the opaque list is not rewound: the span ran
        # twice. (The opaque list exists for the libraries where it matters.)
        assert "val it = 2" in await hol_send("!counter;", session=session)
    finally:
        await hol_stop(session=session)


async def test_rewind_across_an_opaque_span_loads_a_file(tmp_path):
    script = _script(tmp_path, OPAQUE_MARKER)
    session = "rwp_opaque"
    try:
        await _init_file_cursor(file=str(script), session=session)
        await hol_state_at(line=24, col=3, session=session)
        cursor = _sessions[session].cursor
        assert cursor._opaque_points, "the marked span was not seen as opaque"
        assert cursor._checkpoints["b_thm"].context_path is not None
        state = await _edit_b_and_return(script, session)
        assert "=== Goal" in state, state
        # The SaveState file holds the ref as it was: the span ran once since.
        assert "val it = 1" in await hol_send("!counter;", session=session)
    finally:
        await hol_stop(session=session)


async def test_rewind_across_a_module_load_loads_a_file(tmp_path):
    script = tmp_path / "rwmScript.sml"
    script.write_text(THREE_SCRIPT.replace("{marker}", '\nval _ = load "realTheory";')
                      .replace('"rwp"', '"rwm"'))
    session = "rwp_load"
    try:
        await _init_file_cursor(file=str(script), session=session)
        await hol_state_at(line=25, col=3, session=session)
        script.write_text(script.read_text().replace("T /\\ T", "T /\\ T /\\ T"))
        state = await hol_state_at(line=25, col=3, session=session)
        assert "=== Goal" in state and "Error" not in state, state
        assert "thm" in await hol_send("realTheory.REAL_ADD_SYM;", session=session)
        real = await hol_send("Term `real_of_num 1`;", session=session)
        assert "inventing" not in real, real
    finally:
        await hol_stop(session=session)


async def test_gc_keeps_ancestors_and_deletes_the_rest(tmp_path):
    from hol4_mcp.hol_cursor import FileProofCursor
    from hol4_mcp.hol_session import HOLSession
    script = _script(tmp_path)
    session = HOLSession(str(tmp_path))
    await session.start()
    try:
        cursor = FileProofCursor(script, session, checkpoint_dir=tmp_path / "ckpt")
        cursor.SAVESTATE_EVERY = 1
        await cursor.init()
        await cursor.enter_theorem("d_thm")
        files = {n: cursor._checkpoints[n].context_path for n in ("a_thm", "b_thm", "c_thm")}
        assert all(p.exists() for p in files.values())
        # Forget b and c, then load a's file: only a and its ancestors stay.
        for name in ("b_thm", "c_thm"):
            cursor._invalidate_checkpoint(name)
        cursor._checkpoints["a_thm"].point_id = None
        assert await cursor._load_context_checkpoint("a_thm")
        assert files["a_thm"].exists()
        assert not files["b_thm"].exists() and not files["c_thm"].exists()
    finally:
        await session.stop()
