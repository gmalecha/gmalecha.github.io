export default function(eleventyConfig) {
  // Set up excerpt support (equivalent to Jekyll's implicit excerpts)
  eleventyConfig.setFrontMatterParsingOptions({
    excerpt: true,
    excerpt_separator: "<!-- excerpt -->"
  });

  eleventyConfig.setLiquidOptions({
    dynamicPartials: false
  });

  // Since Jekyll excerpt is usually the first paragraph, 
  // we add a custom filter for post excerpt
  eleventyConfig.addFilter("excerpt", (post) => {
    if (post.data.excerpt) return post.data.excerpt;
    if (post.page.excerpt) return post.page.excerpt;
    const content = post.content || '';
    
    // Find the first <p>...</p> block
    const match = content.match(/<p>([\s\S]*?)<\/p>/i);
    if (match) {
      // Strip HTML tags from the paragraph content
      return match[1].replace(/(<([^>]+)>)/gi, "").trim();
    }
    
    // Fallback if no <p> tag is found
    return content.replace(/(<([^>]+)>)/gi, "").trim().substring(0, 200) + "...";
  });

  eleventyConfig.addCollection("posts", function(collectionApi) {
    return collectionApi.getFilteredByGlob("_posts/*.md");
  });

  eleventyConfig.addCollection("publications", function(collectionApi) {
    return collectionApi.getFilteredByGlob("_publications/*.html");
  });

  // Jekyll specific filters used in feed.xml
  eleventyConfig.addFilter("date_to_rfc822", date => {
    if (!date) return "";
    return new Date(date).toUTCString();
  });

  eleventyConfig.addFilter("xml_escape", value => {
    if (!value) return "";
    return value.replace(/&/g, '&amp;')
                .replace(/</g, '&lt;')
                .replace(/>/g, '&gt;')
                .replace(/"/g, '&quot;')
                .replace(/'/g, '&apos;');
  });
  
  // Custom filter for jsonify
  eleventyConfig.addFilter("jsonify", obj => {
    return JSON.stringify(obj);
  });
  
  // Copy static assets
  eleventyConfig.addPassthroughCopy("css");
  eleventyConfig.addPassthroughCopy("js");
  eleventyConfig.addPassthroughCopy("img");
  eleventyConfig.addPassthroughCopy("assets");
  eleventyConfig.addPassthroughCopy(".well-known");

  return {
    dir: {
      input: ".",
      includes: "_includes",
      layouts: "_layouts",
      output: "_site",
      data: "_data"
    }
  };
};
