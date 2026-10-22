"""A passive reading copy. Original Unicode ranges remain authoritative.

Only a small HTML allowlist is emitted. Source offsets, not re-extracted prose,
attach the existing passage records to their original opening elements.
"""
from html import escape
from html.parser import HTMLParser

TAGS = set('a abbr b blockquote br caption cite code dd del dfn div dl dt em h1 h2 h3 h4 h5 h6 hr i li ol p pre q s section small span strong sub sup table tbody td th thead tfoot tr u ul'.split())
VOID = {'br', 'hr'}
DROP = {'script', 'style', 'iframe', 'object', 'embed', 'template', 'svg', 'math'}

class ReadingCopy(HTMLParser):
    def __init__(self, raw, passages):
        super().__init__(convert_charrefs=True)
        self.starts = [0] + [i+1 for i,c in enumerate(raw) if c == '\n']
        self.markers = {}
        for p in passages:
            self.markers.setdefault(p['start'], []).append(p['id'])
        self.seen, self.output, self.suppressed = set(), [], []
        self.feed(raw)
        self.close()
        if self.seen != set(self.markers):
            raise ValueError('A passage cannot be attached to its original HTML opening element')
    def handle_starttag(self, tag, attrs):
        if self.suppressed:
            if tag in DROP:
                self.suppressed.append(tag)
            return
        if tag in DROP:
            self.suppressed.append(tag)
            return
        if tag not in TAGS:
            if tag == 'img':
                self.output.append(escape(dict(attrs).get('alt', '') or ''))
            return
        attrs = dict(attrs)
        safe = {k:v for k,v in attrs.items() if k in {'id','lang','title','colspan','rowspan','start'} and v is not None}
        # Only in-document navigation. Publisher links live in the parent review UI.
        if tag == 'a' and (attrs.get('href') or '').startswith('#'):
            safe['href'] = attrs['href']
        line, col = self.getpos()
        start = self.starts[line-1] + col
        if start in self.markers:
            safe['data-passages'] = ' '.join(self.markers[start])
            self.seen.add(start)
        self.output.append('<' + tag + ''.join(f' {k}="{escape(v, quote=True)}"' for k,v in safe.items()) + '>')
    def handle_endtag(self, tag):
        if self.suppressed:
            if tag == self.suppressed[-1]:
                self.suppressed.pop()
            return
        if tag in TAGS and tag not in VOID:
            self.output.append('</' + tag + '>')
    def handle_startendtag(self, tag, attrs):
        self.handle_starttag(tag, attrs)
        self.handle_endtag(tag)
    def handle_data(self, text):
        if not self.suppressed:
            self.output.append(escape(text))

def reading_copy(raw, passages):
    return ''.join(ReadingCopy(raw, passages).output)
