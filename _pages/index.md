---
# Feel free to add content and custom Front Matter to this file.
# To modify the layout, see https://jekyllrb.com/docs/themes/#overriding-theme-defaults
permalink: /
layout: default
author_profile: false
---

{% assign author = site.author %}

<div id="main">
<div class="profile-container">
    <div class="profile-left">
        <img src="assets/images/bio-photo.jpg" alt="Your Name">
        <div class="contact-info">
          <p>yongweiy at purdue dot com</p>
          <p>
            {% if author.twitter %}
            <li>
            <a href="https://twitter.com/{{ site.author.twitter }}">Twitter</a>
            </li>
            {% endif %}
            {% if author.github %}
            <li>
              <a href="https://github.com/{{ site.author.github }}">GitHub</a>
            </li>
            {% endif %}
          </p>
        </div>
    </div>
    <div class="profile-right">
      {% capture intro %}{% include_relative intro.md %}{% endcapture %}
      {{ intro | markdownify }}
    </div>
</div>
<section class="container" itemprop="text">
  <h1>Publications</h1>
  {% for publication in site.data.publications %}
  <div class='row'>
    <div class='col-conf'>[{{ publication.conference }}]</div>
    <div class='col-paper'>
      <div class='title' display=flex>{{ publication.title }}</div>
      <div class='author'>{{ publication.author | markdownify | remove: '<p>' | remove: '</p>' }}</div>
      <div class="paper-info">
        <div>
          <a class="btn" href="{{ publication.doi }}"><i class="fa fa-globe"></i> doi</a>
          <a class="btn" href="{{ publication.pdf }}"><i class="fa fa-file-pdf"></i> pdf</a>
          <a class="btn" href="{{ publication.artifact }}"><i class="fa fa-code"></i> artifact</a>
          {% if publication.appendix %}
          <a class="btn" href="{{ publication.appendix }}"><i class="fa fa-paperclip"></i> appendix</a>
          {% endif %}
          {% if publication.award %}
          <a class='award'><i class="fa fa-trophy" style="color:gold"></i> <span style="color:tomato">{{ publication.award }}</span></a>
          {% endif %}
        </div>
      </div>
    </div>
  </div>
  {% endfor %}
</section>
</div>