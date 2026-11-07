"""Effectful file prefixes must be reused warm and restored honestly backward."""
from hol4_mcp import hol_mcp_server as srv
from hol4_mcp.hol_session import escape_sml_string


async def test_effectful_prefix_reuse_and_backward_context(tmp_path):
    log = tmp_path / "prefix-executions"
    script = tmp_path / "effectfulScript.sml"
    source = ('open HolKernel Parse boolLib bossLib;\n'
              'val _ = new_theory "effectful";\n'
              'val prefix_marker = ref 0;\n'
              'Theorem first:\n T\nProof\n simp[]\nQED\n'
              'val _ = prefix_marker := !prefix_marker + 1;\n'
              'val _ = let val s = TextIO.openAppend "' + escape_sml_string(str(log)) + '"\n'
              '        in TextIO.output(s,"loaded\\n"); TextIO.closeOut s end;\n'
              'Theorem target:\n T\nProof\n simp[]\nQED\n'
              'val _ = prefix_marker := 99;\n'
              'Theorem later:\n T\nProof\n simp[]\nQED\n')
    script.write_text(source)
    session = "effectful_prefix"
    try:
        checked = await srv.hol_check_proof("target", file=str(script), session=session)
        assert "Status: OK" in checked, checked
        live = srv._sessions[session].session
        pid = live.process.pid
        assert log.read_text().splitlines() == ["loaded"]
        assert "val it = 1:" in await live.send("!prefix_marker;")
        checked = await srv.hol_check_proof("target", session=session)
        assert "Status: OK" in checked
        source = source.replace('Theorem target:\n T\nProof\n simp[]',
                                'Theorem target:\n T\nProof\n rw[]')
        script.write_text(source)
        checked = await srv.hol_check_proof("target", session=session)
        assert "Status: OK" in checked, checked
        assert live.process.pid == pid
        assert log.read_text().splitlines() == ["loaded"], "ordinary target edit replayed the prefix"
        await srv.hol_check_proof("later", session=session)
        assert "val it = 99:" in await live.send("!prefix_marker;")
        cursor = srv._sessions[session].cursor
        target = cursor._get_theorem("target")
        result = await srv.hol_state_at(line=target.proof_end_line - 1, session=session)
        assert "ERROR" not in result and "PROOF BROKEN" not in result, result
        assert "val it = 1:" in await live.send("!prefix_marker;"), "later imperative state leaked backward"
        # Editing a top-level effect must invalidate its prior interpretation.
        script.write_text(source.replace("!prefix_marker + 1", "!prefix_marker + 2"))
        result = await srv.hol_state_at(line=target.proof_end_line - 1, session=session)
        assert "ERROR" not in result and "PROOF BROKEN" not in result, result
        assert "val it = 2:" in await live.send("!prefix_marker;"), "stale/repeated translator state survived edit"
    finally:
        await srv.hol_stop(session)
