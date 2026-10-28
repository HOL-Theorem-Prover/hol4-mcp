"""Every time budget is settable by an environment variable, and the server's
help and tool docstrings state the budget in force."""

import importlib
import inspect

import pytest

from hol4_mcp import budgets
from hol4_mcp import hol_mcp_server as srv

BUDGETS = [
    ("TACTIC_TIMEOUT", "HOL4_MCP_TACTIC_TIMEOUT"),
    ("STATE_AT_TIMEOUT", "HOL4_MCP_STATE_AT_TIMEOUT"),
    ("MAX_STATE_AT_TIMEOUT", "HOL4_MCP_MAX_STATE_AT_TIMEOUT"),
    ("PER_THEOREM_TIMEOUT", "HOL4_MCP_THEOREM_TIMEOUT"),
    ("PREFIX_LOAD_TIMEOUT", "HOL4_MCP_PREFIX_LOAD_TIMEOUT"),
    ("HOLMAKE_TIMEOUT", "HOL4_MCP_HOLMAKE_TIMEOUT"),
    ("MAX_HOLMAKE_TIMEOUT", "HOL4_MCP_MAX_HOLMAKE_TIMEOUT"),
    ("DETACHED_DISCOVERY_TIMEOUT", "HOL4_MCP_DETACHED_DISCOVERY_TIMEOUT"),
]
ALIASES = [
    ("TACTIC_TIMEOUT", "HOL4_MCP_TACTIC_TIMEOUT", "HOL_TACTIC_TIMEOUT"),
    ("STATE_AT_TIMEOUT", "HOL4_MCP_STATE_AT_TIMEOUT", "HOL_STATE_AT_TIMEOUT"),
]


@pytest.fixture
def reload_budgets(monkeypatch):
    """Clear every budget variable; yield a reloader; restore the module."""
    for _, var in BUDGETS:
        monkeypatch.delenv(var, raising=False)
    for _, _, alias in ALIASES:
        monkeypatch.delenv(alias, raising=False)
    yield lambda: importlib.reload(budgets)
    monkeypatch.undo()
    importlib.reload(budgets)


@pytest.mark.parametrize("attr,var", BUDGETS)
def test_budget_reads_its_variable(reload_budgets, monkeypatch, attr, var):
    default = getattr(reload_budgets(), attr)
    value = default + 7
    monkeypatch.setenv(var, str(value))
    assert getattr(reload_budgets(), attr) == value


@pytest.mark.parametrize("attr,var,alias", ALIASES)
def test_old_name_is_an_alias(reload_budgets, monkeypatch, attr, var, alias):
    monkeypatch.setenv(alias, "11")
    assert getattr(reload_budgets(), attr) == 11
    monkeypatch.setenv(var, "13")
    assert getattr(reload_budgets(), attr) == 13


def test_bad_value_names_the_variable(reload_budgets, monkeypatch):
    monkeypatch.setenv("HOL4_MCP_THEOREM_TIMEOUT", "20m")
    with pytest.raises(ValueError, match="HOL4_MCP_THEOREM_TIMEOUT.*'20m'"):
        reload_budgets()


def test_dep_load_timeout_is_read_at_each_call(monkeypatch):
    monkeypatch.delenv("HOL4_MCP_DEP_LOAD_TIMEOUT", raising=False)
    assert budgets.dep_load_timeout() == budgets.DEFAULT_DEP_LOAD_TIMEOUT
    monkeypatch.setenv("HOL4_MCP_DEP_LOAD_TIMEOUT", "42")
    assert budgets.dep_load_timeout() == 42.0


def _serve_help(capsys):
    with pytest.raises(SystemExit):
        srv._cli_parser().parse_args(["serve", "--help"])
    return " ".join(capsys.readouterr().out.split())


def test_help_states_the_budgets_in_force(capsys):
    text = _serve_help(capsys)
    assert f"(default: {budgets.TACTIC_TIMEOUT:g}, from HOL4_MCP_TACTIC_TIMEOUT" in text, text
    assert f"(default: {budgets.STATE_AT_TIMEOUT:g}, from HOL4_MCP_STATE_AT_TIMEOUT" in text, text


def test_help_follows_the_environment(reload_budgets, monkeypatch, capsys):
    monkeypatch.setenv("HOL4_MCP_TACTIC_TIMEOUT", "77")
    reload_budgets()
    assert "(default: 77, from HOL4_MCP_TACTIC_TIMEOUT" in _serve_help(capsys)


def test_tool_docstrings_state_the_budgets_in_force():
    for tool in (srv.hol_state_at, srv.hol_goals):
        doc = " ".join(tool.__doc__.split())
        assert f"server default ({budgets.STATE_AT_TIMEOUT:g}s" in doc, doc
    doc = " ".join(srv.holmake.__doc__.split())
    assert (f"(default {budgets.HOLMAKE_TIMEOUT:g}, max "
            f"{budgets.MAX_HOLMAKE_TIMEOUT:g})") in doc, doc
    assert f"own {budgets.DETACHED_DISCOVERY_TIMEOUT:g}-second safety" in doc, doc
    for tool in (srv.hol_state_at, srv.hol_goals, srv.holmake):
        assert "_TIMEOUT}" not in tool.__doc__
    default = inspect.signature(srv.holmake).parameters["timeout"].default
    assert default == budgets.HOLMAKE_TIMEOUT
