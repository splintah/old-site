{-# LANGUAGE OverloadedStrings #-}

import           Data.Char                (toUpper)
import qualified Data.Map.Strict          as Map
import           Data.Monoid              (mappend)

import           GHC.IO.Encoding          (setLocaleEncoding, utf8)

import           Hakyll
import           Hakyll.Web.Series

import           Text.Pandoc
import           Text.Pandoc.Highlighting
import           Text.Pandoc.Options
import           Text.Pandoc.Walk

main :: IO ()
main = do
  setLocaleEncoding utf8
  hakyll $ do
    ----------------------------------------
    -- Images
    ----------------------------------------
    match "images/*" $ do
      route idRoute
      compile copyFileCompiler

    ----------------------------------------
    -- CSS
    ----------------------------------------
    match "css/*" $ do
      route idRoute
      compile $ compressCssCompiler
        >>= relativizeUrls

    ----------------------------------------
    -- Fonts
    ----------------------------------------
    let anyPattern :: [Pattern] -> Pattern
        anyPattern = foldr1 (.||.)
    match (anyPattern [ "fonts/dejavu/*.ttf"
                      , "fonts/ibm-plex/*.woff2"
                      , "fonts/ibm-plex/*.woff"
                      , "fonts/gentium/*.woff"
                      ]) $ do
      route idRoute
      compile copyFileCompiler

    ----------------------------------------
    -- Special pages
    ----------------------------------------
    -- NOTE: feeds.md file is using Markdown instead of Org mode,
    -- because Pandoc formats the Org mode url [[/atom.xml][Atom]] as a
    -- link to file:///atom.xml.
    match (fromList ["about.org", "feeds.md"]) $ do
      route $ setExtension "html"
      compile $ pandocCompiler
        >>= loadAndApplyTemplate "templates/default.html" defaultContext
        >>= relativizeUrls

    ----------------------------------------
    -- Posts
    ----------------------------------------
    let postsGlob = "posts/*.org"
               .||. "posts/*.md"
               .||. "posts/*.markdown"
               .||. "posts/*.lhs"

    series <- buildSeries postsGlob (fromCapture "series/*.html")

    match postsGlob $ do
      route $ setExtension "html"
      let ctx = postCtxWithSeries series
      compile $ postCompiler
        >>= loadAndApplyTemplate "templates/post.html" ctx
        >>= saveSnapshot "content"
        >>= loadAndApplyTemplate "templates/default.html" ctx
        >>= relativizeUrls

    -- Build series page.
    tagsRules series $ \(s:erie) pat -> do
      let title = toUpper s : erie
      route idRoute
      compile $ do
        posts <- chronological =<< loadAll pat
        let ctx = constField "title" title `mappend`
                  listField "posts" postCtx (pure posts) `mappend`
                  defaultContext
        makeItem ""
          >>= loadAndApplyTemplate "templates/series.html" ctx
          >>= loadAndApplyTemplate "templates/default.html" ctx
          >>= relativizeUrls

    ----------------------------------------
    -- Index
    ----------------------------------------
    match "index.html" $ do
      route idRoute
      compile $ do
        posts <- recentFirst =<< loadAll postsGlob
        let indexCtx =
              listField "posts" postCtx (return posts) `mappend`
              defaultContext

        getResourceBody
          >>= applyAsTemplate indexCtx
          >>= loadAndApplyTemplate "templates/default.html" indexCtx
          >>= relativizeUrls

    ----------------------------------------
    -- Templates
    ----------------------------------------
    match "templates/*" $ compile templateBodyCompiler

    ----------------------------------------
    -- Feeds
    ----------------------------------------
    let compileFeed render = do
          let feedCtx = postCtx `mappend` bodyField "description"
          posts <- recentFirst =<< loadAllSnapshots postsGlob "content"
          render feedConfiguration feedCtx posts

    -- Atom feed
    create ["atom.xml"] $ do
      route idRoute
      compile $ compileFeed renderAtom

    -- RSS feed
    create ["rss.xml"] $ do
      route idRoute
      compile $ compileFeed renderRss

postCompiler :: Compiler (Item String)
postCompiler = pandocCompilerWithTransform
  readerOptions
  writerOptions
    { writerHighlightStyle = Just kate
    , writerSyntaxMap
      -- Add the "Agda2" syntax, which is equal to the "Agda" syntax,
      -- because the Emacs mode is called agda2-mode, and the org-mode
      -- code blocks must therefore begin with "$+begin_src agda2".
      = Map.insert "Agda2" (writerSyntaxMap writerOptions Map.! "Agda")
      $ writerSyntaxMap writerOptions
    , writerExtensions = enableExtension Ext_tex_math_double_backslash $ writerExtensions writerOptions
    , writerHTMLMathMethod = MathJax ""
    }
  transform
  where
    readerOptions = defaultHakyllReaderOptions
    writerOptions = defaultHakyllWriterOptions
    -- Demote all headers in the document, so
    --   # Foo
    --   ## Bar
    -- becomes
    --   <h2>Foo</h2>
    --   <h3>Bar</h3>
    -- because the title of the post is an h1.
    transform = shiftHeaders 1

shiftHeaders :: Int -> Pandoc -> Pandoc
shiftHeaders i p = walk go p
  where
    go (Header l a inl) = Header (l + i) a inl
    go x                = x

postCtx :: Context String
postCtx =
  dateField "date" "%e %B %Y" `mappend`
  defaultContext

postCtxWithSeries :: Tags -> Context String
postCtxWithSeries series = seriesField series `mappend` postCtx

feedConfiguration :: FeedConfiguration
feedConfiguration = FeedConfiguration
  { feedTitle = "Splinter Suidman"
  , feedDescription = "Splinter Suidmans blog"
  , feedAuthorName = "Splinter Suidman"
  , feedAuthorEmail = ""
  , feedRoot = "https://splintah.github.io"
  }
