"""Record the observed execution interruption without counting it as work."""
from pathlib import Path
from datetime import datetime, timezone
import json

root = Path(__file__).resolve().parents[1]
path = root / 'ROUND_STATE.json'
state = json.loads(path.read_text(encoding='utf-8'))
state['goalStatus'] = 'active'
state['goalStatusVerifiedUtc'] = '2026-10-10T02:12:14Z'
state['resumeUtc'] = '2026-10-10T02:12:14Z'
state['excludedUnobservedIntervals'] = [{
    'startUtc': '2026-10-10T00:26:08Z',
    'endUtc': '2026-10-10T02:12:14Z',
    'evidence': 'Last pre-interruption source save and first resumed clock read. '
                'This is an unobserved interval, not an exact process-end timestamp. '
                'The old session handle is missing and no Lean process remained. '
                'It is conservatively excluded from confirmed working-wall-clock duration.'
}]
path.write_text(json.dumps(state, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
with (root / 'RESEARCH_RECORD.md').open('a', encoding='utf-8') as handle:
    handle.write('''

## Execution resume — 2026-10-10 10:12:14 Asia/Shanghai

The external Goal state is now active again, with its full original objective
unchanged. No replacement Goal was created and no completion was claimed.
The last pre-interruption source save was 08:26:08 Asia/Shanghai; the first resumed
clock read was 10:12:14. The former is evidence of a source save, not the exact
time at which the previous Lean process ended. The previous session handle is
missing and no Lean process remained, so the unverified draft was recompiled.
This unobserved interval is conservatively excluded from confirmed working wall
time. The continuous round identifier and original 01:06:01 start are retained;
automatic continuation does not create a new round. Subsequent duration reports
distinguish calendar elapsed time from confirmed working time.
''')
print('Recorded resumed active Goal and excluded unobserved execution interval.')
