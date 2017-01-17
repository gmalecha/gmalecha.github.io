---
---
[ {% for post in site.posts %}{% if post.title %}{{ sep }}{ title: "{{ post.title|strip|smartify }}"
  , date: "{{ post.date }}"
  , url: "{{ post.url }}" }
{% assign sep = ', ' %}{% endif %}{% endfor %}]