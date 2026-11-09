"""Fresh verification must remove stale bindings, not just warning markers."""
import pytest

from hol4_mcp.hol_mcp_server import (
    _sessions, hol_start, hol_stop, hol_state_at, hol_check_proof,
)


def script_text(goal="T", proof="simp[]"):
    return ('open HolKernel Parse boolLib bossLib;\n'
            'val _ = new_theory "freshCheck";\n'
            f'Theorem recovered:\n {goal}\nProof\n {proof}\nQED\n'
            f'Theorem later:\n {goal}\nProof\n ACCEPT_TAC recovered\nQED\n')


async def test_transient_load_failure_can_be_freshly_verified(tmp_path, monkeypatch):
    script = tmp_path / "freshCheckScript.sml"
    script.write_text(script_text())
    session = "fresh_recovery"
    await hol_start(workdir=str(tmp_path), name=session)
    live = _sessions[session].session
    real_send = live.send
    injected = False

    async def fail_first_load(command, timeout=5):
        nonlocal injected
        if not injected and command.lstrip().startswith("Theorem recovered:"):
            injected = True
            return 'Exception- Fail "injected transient load failure" raised\n'
        return await real_send(command, timeout=timeout)

    monkeypatch.setattr(live, "send", fail_first_load)
    try:
        await hol_state_at(file=str(script), line=12, session=session)
        cursor = _sessions[session].cursor
        assert injected and "recovered" in cursor._failed_proofs
        stale = await hol_check_proof(theorem="recovered", session=session)
        assert "Status: NOT VALIDATED" in stale, stale
        old_pid = live.process.pid
        fresh = await hol_check_proof(theorem="recovered", session=session, fresh=True)
        assert "Status: OK" in fresh and "depends on cheat" not in fresh, fresh
        assert "Fresh verification" in fresh
        assert live.process.pid != old_pid
        assert not cursor._failed_proofs
        assert cursor._theorem_oracles["recovered"] == []
        later = await hol_check_proof(theorem="later", session=session)
        assert "Status: OK" in later and "depends on cheat" not in later, later
        assert script.read_text() == script_text()
    finally:
        await hol_stop(session)


async def test_fresh_check_cannot_use_its_own_old_cheated_binding(tmp_path, monkeypatch):
    script = tmp_path / "freshCheckScript.sml"
    script.write_text(script_text("F", "ACCEPT_TAC recovered"))
    session = "fresh_no_self_justification"
    await hol_start(workdir=str(tmp_path), name=session)
    live = _sessions[session].session
    real_send = live.send
    injected = False

    async def fail_first_load(command, timeout=5):
        nonlocal injected
        if not injected and command.lstrip().startswith("Theorem recovered:"):
            injected = True
            return 'Exception- Fail "injected transient load failure" raised\n'
        return await real_send(command, timeout=timeout)

    monkeypatch.setattr(live, "send", fail_first_load)
    try:
        result = await hol_state_at(file=str(script), line=12, session=session)
        assert injected and "recovered" in _sessions[session].cursor._failed_proofs, result
        fresh = await hol_check_proof(theorem="recovered", session=session, fresh=True)
        assert "Status: OK" not in fresh, fresh
        assert "FAILED" in fresh or "ERROR" in fresh, fresh
    finally:
        await hol_stop(session)


async def test_fresh_check_preserves_genuine_dependency_oracles(tmp_path):
    script = tmp_path / "freshCheckScript.sml"
    script.write_text(script_text("F", "cheat"))
    session = "fresh_genuine_cheat"
    try:
        fresh = await hol_check_proof(theorem="later", file=str(script),
                                      session=session, fresh=True)
        assert "depends on cheat" in fresh, fresh
        assert _sessions[session].cursor._theorem_oracles["later"]
    finally:
        await hol_stop(session)


async def test_regular_checks_reuse_verdict_without_restart_or_replay(tmp_path, monkeypatch):
    script = tmp_path / "freshCheckScript.sml"
    script.write_text(script_text())
    session = "ordinary_cached_check"
    try:
        first = await hol_check_proof(theorem="later", file=str(script), session=session)
        assert "Status: OK" in first, first
        live = _sessions[session].session
        cursor = _sessions[session].cursor
        old_pid = live.process.pid
        old_trace = cursor._proof_traces["later"]
        calls = []
        real_send = live.send

        async def recording_send(command, timeout=5):
            calls.append(command)
            return await real_send(command, timeout=timeout)

        monkeypatch.setattr(live, "send", recording_send)
        for _ in range(3):
            result = await hol_check_proof(theorem="later", session=session)
            assert "Status: OK" in result, result
            assert "Fresh verification" not in result
            assert live.process.pid == old_pid
            assert cursor._proof_traces["later"] is old_trace
        assert not any("verify_theorem_json" in c or "loadState" in c
                       or "saveState" in c or c.lstrip().startswith("Theorem ")
                       for c in calls), calls
    finally:
        await hol_stop(session)


async def test_later_admission_is_history_not_dependency_of_earlier_target(tmp_path):
    script = tmp_path / "historyScript.sml"
    script.write_text('open HolKernel Parse boolLib bossLib;\n'
                     'val _ = new_theory "history";\n'
                     'Theorem earlier:\n T\nProof\n simp[]\nQED\n'
                     'Theorem broken:\n F\nProof\n FAIL_TAC "broken load"\nQED\n'
                     'Theorem later:\n T\nProof\n simp[]\nQED\n')
    session = "history_is_not_dependency"
    try:
        await hol_check_proof(theorem="later", file=str(script), session=session)
        cursor = _sessions[session].cursor
        assert "broken" in cursor._failed_proofs
        result = await hol_check_proof(theorem="earlier", session=session)
        assert "Status: OK" in result, result
        assert "context admission history (not a dependency list): broken" in result
        assert "depends on cheat" not in result
        assert cursor._theorem_oracles["earlier"] == []
    finally:
        await hol_stop(session)
