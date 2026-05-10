---
---
[ {% for post in collections.posts %}{% if post.data.title %}{{ sep }}{ title: "{{ post.data.title|strip|smartify }}"
  , date: "{{ post.date }}"
  , url: "{{ post.url }}" }
{% assign sep = ', ' %}{% endif %}{% endfor %}]